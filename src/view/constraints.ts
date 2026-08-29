import type { RegionId } from '../kernel/diagram/diagram'
import type { Engine, RegionCircle } from './engine'
import type { Vec2 } from './vec'
import {
  ancestorRegionIds,
  clampDragToFeasible,
  containedPath,
  recomputeRegions,
} from './relax'

/** A geometric contradiction of the diagram's semantic region tree. `depth` is
    the penetration past the hard bound in world units — the frontier compares
    it against the same conflict's depth in the pre-drag state, so a drag is
    judged by what it CHANGES, not by residuals it merely inherits. */
export type SemanticConflict =
  | {
      readonly kind: 'body-region'
      readonly body: string
      readonly region: RegionId
      readonly depth: number
    }
  | {
      readonly kind: 'region-region'
      readonly first: RegionId
      readonly second: RegionId
      readonly depth: number
    }
  | {
      readonly kind: 'frame-body'
      readonly body: string
      readonly depth: number
    }
  | {
      readonly kind: 'frame-region'
      readonly region: RegionId
      readonly depth: number
    }

const conflictKey = (c: SemanticConflict): string => {
  switch (c.kind) {
    case 'body-region': return `b|${c.body}|${c.region}`
    case 'region-region': return `r|${c.first}|${c.second}`
    case 'frame-body': return `fb|${c.body}`
    case 'frame-region': return `fr|${c.region}`
  }
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
 *
 * The bounds here are SEMANTIC: a disc crossing a drawn cut circle, two cut
 * circles overlapping, content past the border. Aesthetic spacing (sibGap) is
 * deliberately NOT part of them — settled scenes rest AT the gap distance, so a
 * gap-inclusive hard gate would read every rest as wall-to-wall contact and pin
 * any drag that expands a derived circle at fraction 0 (the "existential dots
 * randomly stop" freeze). Restoring the gap after a legal drag is the energy
 * layer's job, which the live settle performs continuously.
 */
export function semanticConflicts(e: Engine): SemanticConflict[] {
  const out: SemanticConflict[] = []

  for (const parent of Object.keys(e.d.regions)) {
    const childIds = e.childrenOf.get(parent) ?? []
    const memberIds = e.membersOf.get(parent) ?? []
    for (const mid of memberIds) {
      const body = e.bodies.get(mid)
      if (body === undefined) continue
      for (const rid of childIds) {
        const region = e.regions.get(rid)
        if (region === undefined) continue
        const need = region.radius + body.discR * e.scale
        const distance = Math.hypot(body.pos.x - region.center.x, body.pos.y - region.center.y)
        if (distance + EPS >= need) continue
        out.push({ kind: 'body-region', body: mid, region: rid, depth: need - distance })
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
        const need = a.radius + b.radius
        const distance = Math.hypot(a.center.x - b.center.x, a.center.y - b.center.y)
        if (distance + EPS >= need) continue
        out.push({ kind: 'region-region', first: aId, second: bId, depth: need - distance })
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
      const off = Math.hypot(correction.x - body.pos.x, correction.y - body.pos.y)
      if (off <= EPS) continue
      out.push({ kind: 'frame-body', body: body.id, depth: off })
    }
    for (const [rid, region] of e.regions) {
      if (rid === e.d.root) continue
      const spill = Math.max(
        minX - (region.center.x - region.radius),
        region.center.x + region.radius - maxX,
        minY - (region.center.y - region.radius),
        region.center.y + region.radius - maxY,
      )
      if (spill <= EPS) continue
      out.push({ kind: 'frame-region', region: rid, depth: spill })
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

/** A drag path with its cumulative arclength, for constant-speed sampling. */
type DragPath = { readonly pts: readonly Vec2[]; readonly cum: readonly number[]; readonly length: number }

function mkDragPath(pts: readonly Vec2[]): DragPath {
  const cum: number[] = [0]
  for (let i = 1; i < pts.length; i++) {
    const a = pts[i - 1]!, b = pts[i]!
    cum.push(cum[i - 1]! + Math.hypot(b.x - a.x, b.y - a.y))
  }
  return { pts, cum, length: cum[cum.length - 1]! }
}

function pathAt(p: DragPath, t: number): Vec2 {
  const s = t * p.length
  for (let i = 1; i < p.pts.length; i++) {
    if (p.cum[i]! < s) continue
    const a = p.pts[i - 1]!, b = p.pts[i]!
    const seg = p.cum[i]! - p.cum[i - 1]!
    const f = seg < 1e-12 ? 0 : (s - p.cum[i - 1]!) / seg
    return { x: a.x + (b.x - a.x) * f, y: a.y + (b.y - a.y) * f }
  }
  return { ...p.pts[p.pts.length - 1]! }
}

/**
 * Project a drag onto the last feasible point ALONG the contained path toward
 * the cursor target.
 *
 * Three layers compose, each owning what the others cannot see:
 *  - the PATH (`containedPath`) walks around foreign region circles, so
 *    intermediate positions never cross a cut — a straight chord to a target
 *    on a cut's far side would;
 *  - the CLAMP projects every candidate pointwise onto its direct hard walls
 *    (foreign circles, frame, ancestor-circle fit), so a committed position is
 *    always feasible for the constraints the clamp owns — gating raw path
 *    points instead would freeze the drag whenever the endpoint's wall-pull is
 *    what makes it legal;
 *  - the GATE rejects candidates that introduce or deepen a SEMANTIC conflict
 *    relative to the pre-drag state — the inverse constraints (this body's
 *    derived ancestor circles expanding over bystanders) that no pointwise
 *    projection of the dragged body can express. Judged relatively because
 *    physics transients can leave residual violations anywhere in the scene;
 *    judged at semantic bounds because rests sit AT the aesthetic gap, and a
 *    gap-inclusive gate reads every rest as contact and pins drags at 0.
 *
 * The returned positions are not committed; callers commit them and recompute
 * regions once, after choosing presentation.
 */
export function projectDragToSemanticFrontier(e: Engine, targets: ReadonlyMap<string, Vec2>): DragProjection {
  const from = new Map<string, Vec2>()
  const paths = new Map<string, DragPath>()
  for (const [id, target] of targets) {
    const body = e.bodies.get(id)
    if (body === undefined) continue
    from.set(id, body.pos)
    paths.set(id, mkDragPath(containedPath(e, body, target)))
  }
  if (paths.size === 0) return { positions: from, requested: from, blocked: false, fraction: 1, conflicts: [] }

  const candidate = (t: number): Map<string, Vec2> => {
    const out = new Map<string, Vec2>()
    for (const [id, path] of paths) out.set(id, clampDragToFeasible(e, e.bodies.get(id)!, pathAt(path, t)))
    return out
  }

  // The gate owns ONLY what the clamp cannot express pointwise: the dragged
  // bodies' derived ancestor circles pressing bystander content. Conflicts the
  // clamp projects directly — a dragged body against a foreign circle or the
  // frame, a dragged ancestor circle against the frame — are skipped: every
  // candidate is already the clamp's fixed point for those, and residuals the
  // clamp legitimately leaves (a spill supported by content this drag cannot
  // move) fluctuate at recompute-noise scale with every candidate, which a
  // strict no-deepening comparison would read as a wall.
  const draggedAncestors = new Set<RegionId>()
  for (const id of paths.keys()) {
    for (const r of ancestorRegionIds(e, e.bodies.get(id)!.region)) {
      const reg = e.d.regions[r]!
      if (reg.kind === 'sheet') break
      draggedAncestors.add(r)
    }
  }
  const clampOwned = (c: SemanticConflict): boolean =>
    (c.kind === 'body-region' && paths.has(c.body)) ||
    (c.kind === 'frame-body' && paths.has(c.body)) ||
    (c.kind === 'frame-region' && draggedAncestors.has(c.region))

  // each remaining conflict may go at most as deep as it already is right now
  // (so the baseline never ratchets deeper across samples); depths at or under
  // the reporting tolerance are absent from both sides by construction
  const allowed = new Map<string, number>()
  for (const c of probeBodyPositions(e, from)) allowed.set(conflictKey(c), c.depth)
  const worsened = (cs: readonly SemanticConflict[]): SemanticConflict[] =>
    cs.filter((c) => !clampOwned(c) && c.depth > (allowed.get(conflictKey(c)) ?? 0))

  const requested = candidate(1)
  const conflicts = worsened(probeBodyPositions(e, requested))
  if (conflicts.length === 0) return { positions: requested, requested, blocked: false, fraction: 1, conflicts: [] }

  let lo = 0
  let hi = 1
  let best: ReadonlyMap<string, Vec2> | null = null
  for (let i = 0; i < FRONTIER_STEPS; i++) {
    const mid = (lo + hi) / 2
    const cand = candidate(mid)
    if (worsened(probeBodyPositions(e, cand)).length === 0) { lo = mid; best = cand }
    else hi = mid
  }
  return {
    positions: best ?? from,
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
