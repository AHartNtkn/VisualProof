import type { Diagram, NodeId, RegionId } from '../../kernel/diagram/diagram'
import type { PathSeg } from '../../kernel/term/reduce'
import { subtermAt } from '../../kernel/term/path'
import { applyFission } from '../../kernel/rules/fusion'
import type { Engine, Body } from '../../view/engine'
import { ascaleOf, frameBounds, localToWorld } from '../../view/engine'
import { bendGrid, type NodeGeometry, type TermOccurrenceGeometry } from '../../view/bend'
import { trompGrid } from '../../view/tromp'
import type { Shape, Theme } from '../../view/paint'
import type { Vec2 } from '../../view/vec'
import { length, polar, sub } from '../../view/vec'
import type { PointerClaim, PointerSample } from './viewport'

const HIT_RADIUS_PX = 7

export type FissionTarget = {
  readonly node: NodeId
  readonly path: readonly PathSeg[]
  readonly occurrence: TermOccurrenceGeometry
  readonly valid: boolean
  readonly reason: string | null
}

export type FissionRequest = {
  readonly node: NodeId
  readonly path: readonly PathSeg[]
  readonly at: Vec2
}

function fissionValidity(diagram: Diagram, node: NodeId, path: readonly PathSeg[]): { valid: boolean; reason: string | null } {
  try {
    applyFission(diagram, node, path)
    return { valid: true, reason: null }
  } catch (error) {
    return { valid: false, reason: error instanceof Error ? error.message : String(error) }
  }
}

function segmentDistance(point: Vec2, a: Vec2, b: Vec2): number {
  const ab = sub(b, a)
  const ap = sub(point, a)
  const d2 = ab.x * ab.x + ab.y * ab.y
  const t = d2 === 0 ? 0 : Math.max(0, Math.min(1, (ap.x * ab.x + ap.y * ab.y) / d2))
  return length(sub(point, { x: a.x + ab.x * t, y: a.y + ab.y * t }))
}

function occurrenceDistance(engine: Engine, body: Body, occurrence: TermOccurrenceGeometry, point: Vec2): number {
  const geometry = body.geometry!
  if (occurrence.hit.kind === 'arcPoint') {
    return length(sub(point, localToWorld(engine, body, occurrence.hit.point)))
  }
  if (occurrence.hit.kind === 'exit') {
    const [a, b] = geometry.exitLine!
    return segmentDistance(point, localToWorld(engine, body, a), localToWorld(engine, body, b))
  }
  const radial = geometry.radials[occurrence.hit.radialIndex]!
  return segmentDistance(
    point,
    localToWorld(engine, body, polar(radial.angle, radial.r0)),
    localToWorld(engine, body, polar(radial.angle, radial.r1)),
  )
}

function comparePath(a: readonly PathSeg[], b: readonly PathSeg[]): number {
  return a.join('/').localeCompare(b.join('/'))
}

export function fissionHit(
  engine: Engine,
  diagram: Diagram,
  world: Vec2,
  viewScale: number,
): FissionTarget | null {
  if (!Number.isFinite(viewScale) || viewScale <= 0) throw new RangeError('fission view scale must be positive')
  const candidates: Array<{ body: Body; occurrence: TermOccurrenceGeometry; distance: number }> = []
  for (const body of engine.bodies.values()) {
    if (body.node?.kind !== 'term' || body.geometry === null) continue
    if (length(sub(world, body.pos)) > body.discR * engine.scale) continue
    for (const occurrence of body.geometry.occurrences) {
      const distance = occurrenceDistance(engine, body, occurrence, world)
      if (distance <= HIT_RADIUS_PX / viewScale) candidates.push({ body, occurrence, distance })
    }
  }
  candidates.sort((a, b) => a.distance - b.distance
    || b.occurrence.depth - a.occurrence.depth
    || comparePath(a.occurrence.path, b.occurrence.path)
    || a.body.id.localeCompare(b.body.id))
  const found = candidates[0]
  if (found === undefined || diagram.nodes[found.body.id]?.kind !== 'term') return null
  const validity = fissionValidity(diagram, found.body.id, found.occurrence.path)
  return { node: found.body.id, path: found.occurrence.path, occurrence: found.occurrence, ...validity }
}

function anatomyShapes(engine: Engine, body: Body, occurrence: TermOccurrenceGeometry, color: string): Shape[] {
  const geometry = body.geometry!
  const scale = ascaleOf(body.kind) * engine.scale
  const shapes: Shape[] = []
  for (const index of occurrence.arcIndices) {
    const arc = geometry.arcs[index]
    if (arc !== undefined) shapes.push({
      kind: 'arc', center: body.pos, r: arc.r * scale,
      a0: arc.a0 + body.theta, a1: arc.a1 + body.theta,
      stroke: color, width: 4.5, glow: null,
    })
  }
  for (const index of occurrence.radialIndices) {
    const radial = geometry.radials[index]
    if (radial !== undefined) shapes.push({
      kind: 'segment',
      from: localToWorld(engine, body, polar(radial.angle, radial.r0)),
      to: localToWorld(engine, body, polar(radial.angle, radial.r1)),
      stroke: color, width: 4.5, glow: null,
    })
  }
  if (occurrence.includeExit) {
    if (geometry.exitArc !== null) shapes.push({
      kind: 'arc', center: body.pos, r: geometry.exitArc.r * scale,
      a0: geometry.exitArc.a0 + body.theta, a1: geometry.exitArc.a1 + body.theta,
      stroke: color, width: 4.5, glow: null,
    })
    if (geometry.exitLine !== null) shapes.push({
      kind: 'segment', from: localToWorld(engine, body, geometry.exitLine[0]),
      to: localToWorld(engine, body, geometry.exitLine[1]), stroke: color, width: 4.5, glow: null,
    })
  }
  return shapes
}

function hitPoint(engine: Engine, body: Body, occurrence: TermOccurrenceGeometry): Vec2 {
  if (occurrence.hit.kind === 'arcPoint') return localToWorld(engine, body, occurrence.hit.point)
  if (occurrence.hit.kind === 'exit') return localToWorld(engine, body, body.geometry!.exitLine![0])
  const radial = body.geometry!.radials[occurrence.hit.radialIndex]!
  return localToWorld(engine, body, polar(radial.angle, (radial.r0 + radial.r1) / 2))
}

export function fissionTargetPoint(engine: Engine, node: NodeId, path: readonly PathSeg[]): Vec2 | null {
  const body = engine.bodies.get(node)
  if (body === undefined || body.geometry === null) return null
  const occurrence = body.geometry.occurrences.find((candidate) => candidate.path.length === path.length
    && candidate.path.every((segment, index) => segment === path[index]))
  return occurrence === undefined ? null : hitPoint(engine, body, occurrence)
}

function geometryShapesAt(engine: Engine, geometry: NodeGeometry, at: Vec2, color: string): Shape[] {
  const scale = ascaleOf('term') * engine.scale
  const shapes: Shape[] = geometry.arcs.map((arc) => ({
    kind: 'arc', center: at, r: arc.r * scale, a0: arc.a0, a1: arc.a1,
    stroke: color, width: 2.3, glow: null,
  }))
  for (const radial of geometry.radials) shapes.push({
    kind: 'segment',
    from: { x: at.x + Math.cos(radial.angle) * radial.r0 * scale, y: at.y + Math.sin(radial.angle) * radial.r0 * scale },
    to: { x: at.x + Math.cos(radial.angle) * radial.r1 * scale, y: at.y + Math.sin(radial.angle) * radial.r1 * scale },
    stroke: color, width: 2.3, glow: null,
  })
  if (geometry.exitLine !== null) shapes.push({
    kind: 'segment',
    from: { x: at.x + geometry.exitLine[0].x * scale, y: at.y + geometry.exitLine[0].y * scale },
    to: { x: at.x + geometry.exitLine[1].x * scale, y: at.y + geometry.exitLine[1].y * scale },
    stroke: color, width: 2.3, glow: null,
  })
  return shapes
}

function directRegionAt(engine: Engine, diagram: Diagram, point: Vec2): RegionId {
  let best: { readonly id: RegionId; readonly radius: number } | null = null
  for (const [id, region] of engine.regions) {
    if (diagram.regions[id]?.kind === 'sheet') continue
    if (length(sub(point, region.center)) <= region.radius && (best === null || region.radius < best.radius)) {
      best = { id, radius: region.radius }
    }
  }
  return best?.id ?? diagram.root
}

function insideFrame(engine: Engine, point: Vec2): boolean {
  const bounds = frameBounds(engine)
  return bounds === null || (bounds.minX <= point.x && point.x <= bounds.maxX && bounds.minY <= point.y && point.y <= bounds.maxY)
}

function placementValid(engine: Engine, diagram: Diagram, nodeId: NodeId, at: Vec2): boolean {
  if (!insideFrame(engine, at)) return false
  const body = engine.bodies.get(nodeId)
  const node = diagram.nodes[nodeId]
  if (body === undefined || node?.kind !== 'term') return false
  if (length(sub(at, body.pos)) <= body.discR * engine.scale) return false
  return directRegionAt(engine, diagram, at) === node.region
}

export function fissionDropPoint(engine: Engine, diagram: Diagram, nodeId: NodeId): Vec2 | null {
  const body = engine.bodies.get(nodeId)
  if (body === undefined) return null
  const distance = body.discR * engine.scale + 2
  for (let index = 0; index < 32; index += 1) {
    const angle = index * Math.PI / 16
    const candidate = {
      x: body.pos.x + Math.cos(angle) * distance,
      y: body.pos.y + Math.sin(angle) * distance,
    }
    if (placementValid(engine, diagram, nodeId, candidate)) return candidate
  }
  return null
}

export type FissionDragOptions = {
  readonly active: () => boolean
  readonly diagram: () => Diagram
  readonly engine: () => Engine
  readonly viewScale: () => number
  readonly theme: () => Theme
  readonly commit: (request: FissionRequest) => void
  readonly refuse: (text: string, pointer: Vec2) => void
}

type DragPreview = { readonly target: FissionTarget; at: Vec2; placementValid: boolean; moved: boolean }

export class FissionDragController {
  readonly #options: FissionDragOptions
  #hover: FissionTarget | null = null
  #drag: DragPreview | null = null
  #ctrlHeld = false
  #generation = 0

  constructor(options: FissionDragOptions) { this.#options = options }

  hover(sample: PointerSample | null): void {
    if (sample === null || !this.#options.active() || sample.ctrlKey || sample.shiftKey || this.#ctrlHeld || this.#drag !== null) {
      this.#hover = null
      return
    }
    this.#hover = fissionHit(this.#options.engine(), this.#options.diagram(), sample.world, this.#options.viewScale())
  }

  modifiersChanged(ctrlHeld: boolean): void {
    this.#ctrlHeld = ctrlHeld
    if (ctrlHeld) this.cancel()
  }

  claim(sample: PointerSample): PointerClaim | null {
    if (!this.#options.active() || sample.button !== 0 || sample.shiftKey || sample.ctrlKey || this.#ctrlHeld) return null
    const target = fissionHit(this.#options.engine(), this.#options.diagram(), sample.world, this.#options.viewScale())
    if (target === null) return null
    const preview: DragPreview = { target, at: sample.world, placementValid: false, moved: false }
    const generation = ++this.#generation
    const current = (): boolean => this.#generation === generation && this.#drag === preview && this.#options.active()
    this.#drag = preview
    this.#hover = null
    return {
      still: 'selection',
      blocksPassiveRelaxation: true,
      move: (next) => {
        if (!current()) return
        preview.at = next.world
        preview.moved = true
        preview.placementValid = this.#placementValid(preview)
      },
      release: (next, moved) => {
        if (!current()) return
        this.#drag = null
        this.#generation++
        if (!moved) return
        const validity = fissionValidity(this.#options.diagram(), target.node, target.path)
        if (!validity.valid) {
          this.#options.refuse(validity.reason ?? 'this subterm cannot be split out', next.client)
          return
        }
        if (!placementValid(this.#options.engine(), this.#options.diagram(), target.node, next.world)) {
          this.#options.refuse('pull outside the node and release in its current region to fission', next.client)
          return
        }
        try {
          this.#options.commit({ node: target.node, path: target.path, at: next.world })
        } catch (error) {
          this.#options.refuse(error instanceof Error ? error.message : String(error), next.client)
        }
      },
      cancel: () => { if (current()) this.cancel() },
    }
  }

  overlay(): readonly Shape[] {
    if (!this.#options.active()) {
      this.cancel()
      return []
    }
    const target = this.#drag?.target ?? this.#hover
    if (target === null) return []
    const body = this.#options.engine().bodies.get(target.node)
    if (body === undefined || body.geometry === null) return []
    const preview = this.#drag
    const validity = fissionValidity(this.#options.diagram(), target.node, target.path)
    const valid = validity.valid && (preview === null || !preview.moved || preview.placementValid)
    const color = valid ? this.#options.theme().interaction.valid : this.#options.theme().interaction.refusal
    const shapes = anatomyShapes(this.#options.engine(), body, target.occurrence, color)
    if (preview !== null && preview.moved) {
      shapes.push({ kind: 'segment', from: hitPoint(this.#options.engine(), body, target.occurrence), to: preview.at,
        stroke: color, width: 1.8, glow: null })
      const node = this.#options.diagram().nodes[target.node]
      if (validity.valid && node?.kind === 'term') {
        try {
          const subterm = subtermAt(node.term, target.path)
          shapes.push(...geometryShapesAt(this.#options.engine(), bendGrid(trompGrid(subterm)), preview.at, color))
        } catch {
          // Current validity is the authority; a concurrent path change simply leaves the red drag trace.
        }
      }
    }
    return shapes
  }

  cancel(): boolean {
    const hadState = this.#drag !== null || this.#hover !== null
    this.#generation++
    this.#drag = null
    this.#hover = null
    return hadState
  }
  dispose(): void { this.cancel() }

  #placementValid(preview: DragPreview): boolean {
    return preview.target.valid
      && placementValid(this.#options.engine(), this.#options.diagram(), preview.target.node, preview.at)
  }
}
