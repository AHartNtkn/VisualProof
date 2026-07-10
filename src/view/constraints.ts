import type { RegionId } from '../kernel/diagram/diagram'
import type { Engine, RegionCircle } from './engine'
import type { Vec2 } from './vec'
import { clampDragToFeasible, PACE, recomputeRegions } from './relax'

/** A geometric contradiction of the diagram's semantic region tree. */
export type SemanticConflict =
  | {
      readonly kind: 'body-region'
      readonly body: string
      readonly region: RegionId
    }
  | {
      readonly kind: 'region-region'
      readonly first: RegionId
      readonly second: RegionId
    }
  | {
      readonly kind: 'frame-body'
      readonly body: string
    }
  | {
      readonly kind: 'frame-region'
      readonly region: RegionId
    }

export type DragProjection = {
  readonly positions: ReadonlyMap<string, Vec2>
  readonly requested: ReadonlyMap<string, Vec2>
  readonly blocked: boolean
  readonly fraction: number
  readonly conflicts: readonly SemanticConflict[]
}

const EPS = 0.04
const FRONTIER_STEPS = 26

/**
 * The complete hard geometry contract for the semantic region tree.
 *
 * Region circles are derived, not stateful containers. Legality is therefore
 * checked at each parent boundary: every direct member must be outside every
 * child region it does not belong to, sibling child regions must be disjoint,
 * and all visible content must remain within the fixed proof frame. Because a
 * child circle encloses its whole subtree, these local checks imply the same
 * relation for every non-ancestor region in the diagram.
 */
export function semanticConflicts(e: Engine): SemanticConflict[] {
  const out: SemanticConflict[] = []
  const gap = PACE.sibGap * e.scale

  for (const parent of Object.keys(e.d.regions)) {
    const childIds = e.childrenOf.get(parent) ?? []
    const memberIds = e.membersOf.get(parent) ?? []
    for (const mid of memberIds) {
      const body = e.bodies.get(mid)
      if (body === undefined) continue
      for (const rid of childIds) {
        const region = e.regions.get(rid)
        if (region === undefined) continue
        const need = body.kind === 'junction'
          ? region.radius
          : region.radius + body.discR * e.scale + gap
        const distance = Math.hypot(body.pos.x - region.center.x, body.pos.y - region.center.y)
        if (distance + EPS >= need) continue
        out.push({ kind: 'body-region', body: mid, region: rid })
      }
    }
    for (let i = 0; i < childIds.length; i++) {
      const aId = childIds[i]!
      const a = e.regions.get(aId)
      if (a === undefined) continue
      for (let j = i + 1; j < childIds.length; j++) {
        const bId = childIds[j]!
        const b = e.regions.get(bId)
        if (b === undefined) continue
        const need = a.radius + b.radius + gap
        if (Math.hypot(a.center.x - b.center.x, a.center.y - b.center.y) + EPS >= need) continue
        out.push({ kind: 'region-region', first: aId, second: bId })
      }
    }
  }

  const frame = e.frame
  if (frame !== null) {
    const minX = frame.center.x - frame.half
    const maxX = frame.center.x + frame.half
    const minY = frame.center.y - frame.half
    const maxY = frame.center.y + frame.half
    for (const body of e.bodies.values()) {
      const r = body.discR * e.scale
      const correction = {
        x: Math.max(minX + r, Math.min(maxX - r, body.pos.x)),
        y: Math.max(minY + r, Math.min(maxY - r, body.pos.y)),
      }
      if (Math.hypot(correction.x - body.pos.x, correction.y - body.pos.y) <= EPS) continue
      out.push({ kind: 'frame-body', body: body.id })
    }
    for (const [rid, region] of e.regions) {
      if (rid === e.d.root) continue
      if (
        region.center.x - region.radius >= minX - EPS &&
        region.center.x + region.radius <= maxX + EPS &&
        region.center.y - region.radius >= minY - EPS &&
        region.center.y + region.radius <= maxY + EPS
      ) continue
      out.push({ kind: 'frame-region', region: rid })
    }
  }
  return out
}

function restoreRegions(e: Engine, saved: ReadonlyMap<RegionId, RegionCircle>): void {
  e.regions.clear()
  for (const [id, circle] of saved) e.regions.set(id, circle)
}

/** Probe a candidate without leaking body positions or derived circle state. */
export function probeBodyPositions(e: Engine, positions: ReadonlyMap<string, Vec2>): SemanticConflict[] {
  const savedBodies = new Map<string, Vec2>()
  const savedRegions = new Map(e.regions)
  const dirty = new Set<RegionId>()
  for (const [id, pos] of positions) {
    const body = e.bodies.get(id)
    if (body === undefined) continue
    savedBodies.set(id, body.pos)
    body.pos = pos
    dirty.add(body.region)
  }
  recomputeRegions(e, dirty)
  const conflicts = semanticConflicts(e)
  for (const [id, pos] of savedBodies) e.bodies.get(id)!.pos = pos
  restoreRegions(e, savedRegions)
  return conflicts
}

function interpolate(from: ReadonlyMap<string, Vec2>, to: ReadonlyMap<string, Vec2>, t: number): Map<string, Vec2> {
  const out = new Map<string, Vec2>()
  for (const [id, end] of to) {
    const start = from.get(id)
    if (start === undefined) continue
    out.set(id, { x: start.x + (end.x - start.x) * t, y: start.y + (end.y - start.y) * t })
  }
  return out
}

/**
 * Project a drag onto the first semantic-feasibility frontier.
 *
 * The existing single-body projection owns direct foreign-region and frame
 * contact. This layer adds the inverse constraint that projection cannot see:
 * moving a member may expand its derived ancestor circle across a sibling body
 * or region. The returned positions are not committed; callers commit them and
 * recompute regions once, after choosing presentation.
 */
export function projectDragToSemanticFrontier(e: Engine, targets: ReadonlyMap<string, Vec2>): DragProjection {
  const from = new Map<string, Vec2>()
  const requested = new Map<string, Vec2>()
  for (const [id, target] of targets) {
    const body = e.bodies.get(id)
    if (body === undefined) continue
    from.set(id, body.pos)
    requested.set(id, clampDragToFeasible(e, body, target))
  }
  if (requested.size === 0) return { positions: from, requested, blocked: false, fraction: 1, conflicts: [] }

  const conflicts = probeBodyPositions(e, requested)
  if (conflicts.length === 0) return { positions: requested, requested, blocked: false, fraction: 1, conflicts: [] }

  let lo = 0
  let hi = 1
  for (let i = 0; i < FRONTIER_STEPS; i++) {
    const mid = (lo + hi) / 2
    if (probeBodyPositions(e, interpolate(from, requested, mid)).length === 0) lo = mid
    else hi = mid
  }
  return {
    positions: interpolate(from, requested, lo),
    requested,
    blocked: true,
    fraction: lo,
    conflicts,
  }
}

/** Commit a previously projected position set and synchronize derived circles. */
export function commitBodyPositions(e: Engine, positions: ReadonlyMap<string, Vec2>): void {
  const dirty = new Set<RegionId>()
  for (const [id, pos] of positions) {
    const body = e.bodies.get(id)
    if (body === undefined) continue
    body.pos = pos
    dirty.add(body.region)
  }
  recomputeRegions(e, dirty)
}
