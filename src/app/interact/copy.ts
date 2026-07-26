import type { Diagram } from '../../kernel/diagram/diagram'
import { selectionContents, type SubgraphSelection } from '../../kernel/diagram/subgraph/selection'
import type { Engine } from '../../view/engine'
import type { Shape, Theme } from '../../view/paint'
import { absorbHits } from '../edit'
import { buildSelection, type Hit } from '../hit-selection'
import {
  planCopy,
  revalidateCopy,
  type CopyDestination,
  type CopyPlan,
  type CopyRefusal,
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
  readonly sourcePreview?: (
    engine: Engine,
    selection: SubgraphSelection,
    theme: Theme,
  ) => readonly Shape[]
  readonly destinationPreview?: (destination: CopyDestination, plan: CopyPlan) => readonly Shape[]
}

type CopyDrag = {
  readonly source: Diagram
  readonly selection: SubgraphSelection
  planned: CopyPlan | CopyRefusal | null
  destination: CopyDestination | null
  moved: boolean
  current: boolean
  sample: PointerSample
}

/** Shared ownership for selected-pattern copy gestures. All semantic target
    discovery and revalidation is delegated to CopyPlanner. */
export class CopyDragController {
  readonly #options: CopyDragControllerOptions
  #drag: CopyDrag | null = null

  constructor(options: CopyDragControllerOptions) {
    this.#options = options
  }

  get dragging(): boolean { return this.#drag?.current === true }

  claim(sample: PointerSample): PointerClaim | null {
    if (!this.#options.active() || sample.button !== 0 || sample.ctrlKey || sample.shiftKey) return null
    const hits = this.#options.sourceSelection()
    if (sample.hit === null) return null
    let selection: SubgraphSelection
    const source = this.#options.sourceDiagram()
    try {
      selection = buildSelection(source, absorbHits(source, hits))
    } catch {
      return null
    }
    const contents = selectionContents(source, selection)
    const onSelectedSurface = sample.hit.kind === 'node'
      ? contents.allNodes.has(sample.hit.id)
      : sample.hit.kind === 'region'
        ? contents.allRegions.has(sample.hit.id)
        : contents.internalWires.includes(sample.hit.id)
    if (!onSelectedSurface) return null
    const drag: CopyDrag = {
      source,
      selection,
      planned: null,
      destination: null,
      moved: false,
      current: true,
      sample,
    }
    this.#drag = drag
    return {
      still: 'selection',
      blocksPassiveRelaxation: false,
      move: (next) => {
        if (!drag.current || this.#drag !== drag || !this.#options.active()) return
        if (next.ctrlKey) { this.#cancel(drag); return }
        drag.moved = true
        drag.sample = next
        const destination = this.#options.destination(next)
        drag.destination = destination
        if (destination === null) {
          drag.planned = null
          return
        }
        drag.planned = planCopy(drag.source, drag.selection, destination)
      },
      release: (next, moved) => {
        if (next.ctrlKey) { this.#cancel(drag); return }
        if (!drag.current || this.#drag !== drag) return
        this.#drag = null
        drag.current = false
        if (!moved || !drag.moved || drag.destination === null) return
        const liveDestination = this.#options.destination(next)
        if (liveDestination === null) return
        const planned = planCopy(drag.source, drag.selection, liveDestination)
        if (planned.kind === 'refusal') {
          this.#options.refuse(planned.message, next)
          return
        }
        const checked = revalidateCopy(
          planned,
          this.#options.sourceDiagram(),
          liveDestination,
        )
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
    if (drag === null || !drag.current || !drag.moved || drag.planned === null
      || drag.planned.kind === 'refusal' || drag.destination === null
      || !this.#options.active()) return null
    const destination = this.#options.destination(drag.sample)
    if (destination === null) return null
    return revalidateCopy(
      drag.planned,
      this.#options.sourceDiagram(),
      destination,
    ).kind === 'refusal' ? null : drag
  }

  #sourceShapes(drag: CopyDrag): readonly Shape[] {
    return this.#options.sourcePreview?.(
      this.#options.sourceEngine(),
      drag.selection,
      this.#options.theme(),
    ) ?? []
  }

  #destinationShapes(drag: CopyDrag): readonly Shape[] {
    if (
      drag.destination === null
      || drag.planned === null
      || drag.planned.kind === 'refusal'
    ) return []
    return this.#options.destinationPreview?.(
      drag.destination,
      drag.planned,
    ) ?? []
  }
}
