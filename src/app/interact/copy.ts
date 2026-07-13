import type { Diagram, RegionId } from '../../kernel/diagram/diagram'
import type { SubgraphSelection } from '../../kernel/diagram/subgraph/selection'
import type { Engine } from '../../view/engine'
import type { Shape, Theme } from '../../view/paint'
import { existentialStubs, legPaths } from '../../view/wires'
import { absorbHits } from '../edit'
import { buildSelection, type Hit } from '../hittest'
import {
  planCopy,
  revalidateCopy,
  type CopyDestination,
  type CopyPlan,
} from '../copy-planner'
import type { PointerClaim, PointerSample } from './viewport'

export type CopyDragControllerOptions = {
  readonly active: () => boolean
  readonly sourceDiagram: () => Diagram
  readonly sourceSelection: () => readonly Hit[]
  readonly sourceEngine: () => Engine
  readonly viewScale: () => number
  readonly destination: (sample: PointerSample) => CopyDestination | null
  readonly commit: (plan: CopyPlan, sample: PointerSample) => void
  readonly refuse: (text: string, sample: PointerSample) => void
  readonly theme: () => Theme
  readonly destinationPreview?: (destination: CopyDestination, plan: CopyPlan) => readonly Shape[]
}

type CopyDrag = {
  readonly source: Diagram
  readonly selection: SubgraphSelection
  plan: CopyPlan | null
  destination: CopyDestination | null
  moved: boolean
  current: boolean
  sample: PointerSample
}

function sameHit(a: Hit, b: Hit): boolean {
  return a.kind === b.kind && a.id === b.id
}

export function copyRegionAt(engine: Engine, diagram: Diagram, point: { readonly x: number; readonly y: number }): RegionId {
  let best: { readonly id: RegionId; readonly radius: number } | null = null
  for (const [id, geometry] of engine.regions) {
    if (diagram.regions[id]?.kind === 'sheet') continue
    if (Math.hypot(point.x - geometry.center.x, point.y - geometry.center.y) <= geometry.radius
      && (best === null || geometry.radius < best.radius)) best = { id, radius: geometry.radius }
  }
  return best?.id ?? diagram.root
}

export function copyDestinationPreview(engine: Engine, region: RegionId, theme: Theme): readonly Shape[] {
  const geometry = engine.regions.get(region)
  if (geometry === undefined) return []
  const color = theme.interaction.valid
  return [{
    kind: 'circle', center: geometry.center, r: geometry.radius,
    fill: `${color}22`, stroke: color, width: 2.4, insetColor: null, glow: null,
  }]
}

function selectionShapes(engine: Engine, selection: SubgraphSelection, stroke: string): Shape[] {
  const shapes: Shape[] = []
  for (const node of selection.nodes) {
    const body = engine.bodies.get(node)
    if (body !== undefined) shapes.push({
      kind: 'circle', center: body.pos, r: body.discR * engine.scale + 2,
      fill: null, stroke, width: 2.5, insetColor: null, glow: null,
    })
  }
  for (const region of selection.regions) {
    const geometry = engine.regions.get(region)
    if (geometry !== undefined) shapes.push({
      kind: 'circle', center: geometry.center, r: geometry.radius,
      fill: null, stroke, width: 2.5, insetColor: null, glow: null,
    })
  }
  const wires = new Set(selection.wires)
  for (const path of legPaths(engine)) if (wires.has(path.wid)) {
    shapes.push({ kind: 'polyline', pts: path.pts, stroke, width: 3, glow: null })
  }
  for (const stub of existentialStubs(engine)) if (wires.has(stub.wid)) {
    shapes.push({ kind: 'segment', from: stub.from, to: stub.to, stroke, width: 3, glow: null })
  }
  return shapes
}

/** Shared ownership for selected-pattern copy gestures. All semantic target
    discovery and revalidation is delegated to CopyPlanner. */
export class CopyDragController {
  readonly #options: CopyDragControllerOptions
  #drag: CopyDrag | null = null

  constructor(options: CopyDragControllerOptions) {
    this.#options = options
  }

  claim(sample: PointerSample): PointerClaim | null {
    if (!this.#options.active() || sample.button !== 0 || sample.ctrlKey || sample.shiftKey) return null
    const hits = this.#options.sourceSelection()
    if (sample.hit === null || !hits.some((hit) => sameHit(hit, sample.hit!))) return null
    let selection: SubgraphSelection
    const source = this.#options.sourceDiagram()
    try {
      selection = buildSelection(source, absorbHits(source, hits))
    } catch {
      return null
    }
    const drag: CopyDrag = { source, selection, plan: null, destination: null, moved: false, current: true, sample }
    this.#drag = drag
    return {
      still: 'selection',
      blocksPassiveRelaxation: false,
      move: (next) => {
        if (!drag.current || this.#drag !== drag || !this.#options.active()) return
        drag.moved = true
        drag.sample = next
        const destination = this.#options.destination(next)
        drag.destination = destination
        if (destination === null) {
          drag.plan = null
          return
        }
        const planned = planCopy(drag.source, drag.selection, destination)
        drag.plan = planned.kind === 'refusal' ? null : planned
      },
      release: (next, moved) => {
        if (!drag.current || this.#drag !== drag) return
        this.#drag = null
        drag.current = false
        if (!moved || !drag.moved || drag.plan === null || drag.destination === null) return
        const liveDestination = this.#options.destination(next)
        if (liveDestination === null) return
        const checked = revalidateCopy(drag.plan, this.#options.sourceDiagram(), liveDestination)
        if (checked.kind === 'refusal') {
          this.#options.refuse(checked.message, next)
          return
        }
        try {
          this.#options.commit(checked, next)
        } catch (error) {
          this.#options.refuse(error instanceof Error ? error.message : String(error), next)
        }
      },
      cancel: () => this.#cancel(drag),
    }
  }

  overlay(): readonly Shape[] {
    const drag = this.#previewableDrag()
    if (drag === null) return []
    return [...this.#sourceShapes(drag), ...this.#destinationShapes(drag)]
  }

  sourceOverlay(): readonly Shape[] {
    const drag = this.#previewableDrag()
    return drag === null ? [] : this.#sourceShapes(drag)
  }

  destinationOverlay(): readonly Shape[] {
    const drag = this.#previewableDrag()
    return drag === null ? [] : this.#destinationShapes(drag)
  }

  cancel(): void {
    if (this.#drag !== null) this.#cancel(this.#drag)
  }

  modifiersChanged(ctrlHeld: boolean): void {
    if (ctrlHeld) this.cancel()
  }

  dispose(): void { this.cancel() }

  #cancel(drag: CopyDrag): void {
    drag.current = false
    if (this.#drag === drag) this.#drag = null
  }

  #previewableDrag(): CopyDrag | null {
    const drag = this.#drag
    if (drag === null || !drag.current || !drag.moved || drag.plan === null || drag.destination === null
      || !this.#options.active()) return null
    const destination = this.#options.destination(drag.sample)
    if (destination === null) return null
    return revalidateCopy(drag.plan, this.#options.sourceDiagram(), destination).kind === 'refusal' ? null : drag
  }

  #sourceShapes(drag: CopyDrag): readonly Shape[] {
    return selectionShapes(this.#options.sourceEngine(), drag.selection, this.#options.theme().interaction.valid)
  }

  #destinationShapes(drag: CopyDrag): readonly Shape[] {
    if (drag.destination === null || drag.plan === null) return []
    return this.#options.destinationPreview?.(drag.destination, drag.plan) ?? []
  }
}
