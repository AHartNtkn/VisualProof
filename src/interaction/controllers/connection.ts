import type { Endpoint, WireId } from '../../kernel/diagram/diagram'
import { pkey, type Engine } from '../../view/engine'
import type { Shape, Theme } from '../../view/paint'
import type { Vec2 } from '../../view/vec'
import { computeLegs, existentialStubs, legPaths } from '../../view/wires'
import { wireManipulationHitTest } from '../hittest'
import type { PointerClaim, PointerSample } from './viewport'

export type ConnectionEnd = {
  readonly wire: WireId
  readonly endpoint: Endpoint | null
}

export type ConnectionDragOptions = {
  readonly active: () => boolean
  readonly engine: () => Engine
  readonly viewScale: () => number
  readonly theme: () => Theme
  readonly commit: (source: ConnectionEnd, target: ConnectionEnd, pointer: Vec2) => boolean
  readonly refuse: (text: string, pointer: Vec2) => void
}

type ConnectionPreview = {
  readonly source: ConnectionEnd
  readonly from: Vec2
  at: Vec2
  target: ConnectionEnd | null
}

function wireShapes(engine: Engine, wire: WireId, stroke: string, width: number): Shape[] {
  const out: Shape[] = []
  for (const path of legPaths(engine)) {
    if (path.wid === wire) out.push({ kind: 'polyline', pts: path.pts, stroke, width, glow: null })
  }
  for (const stub of existentialStubs(engine)) {
    if (stub.wid === wire) out.push({ kind: 'segment', from: stub.from, to: stub.to, stroke, width, glow: null })
  }
  return out
}

function targetShapes(engine: Engine, target: ConnectionEnd, stroke: string, width: number): Shape[] {
  if (target.endpoint === null) return wireShapes(engine, target.wire, stroke, width)
  const key = pkey(target.endpoint.port)
  return computeLegs(engine)
    .filter(({ leg }) => leg.wid === target.wire && (
      (leg.from.body === target.endpoint!.node && leg.from.key === key)
      || (leg.to.body === target.endpoint!.node && leg.to.key === key)
    ))
    .map(({ pts }): Shape => ({ kind: 'polyline', pts, stroke, width, glow: null }))
}

/** One connection gesture for every canvas mode. Mode-specific policy decides
    what a source/target pair means; capture, hit testing, and preview do not. */
export class ConnectionDragController {
  readonly #options: ConnectionDragOptions
  #preview: ConnectionPreview | null = null

  constructor(options: ConnectionDragOptions) { this.#options = options }

  claim(sample: PointerSample): PointerClaim | null {
    if (!this.#options.active() || sample.button !== 0 || sample.shiftKey || sample.ctrlKey) return null
    const hit = wireManipulationHitTest(this.#options.engine(), sample.world, { scale: this.#options.viewScale() })
    if (hit === null) return null
    const preview: ConnectionPreview = {
      source: { wire: hit.wire, endpoint: hit.endpoint },
      from: sample.world,
      at: sample.world,
      target: null,
    }
    this.#preview = preview
    return {
      still: 'selection',
      blocksPassiveRelaxation: true,
      move: (next) => {
        preview.at = next.world
        const target = wireManipulationHitTest(this.#options.engine(), next.world, { scale: this.#options.viewScale() })
        preview.target = target === null ? null : { wire: target.wire, endpoint: target.endpoint }
      },
      release: (next, moved) => {
        this.#preview = null
        if (!moved) return
        if (preview.target === null) {
          this.#options.refuse('release on a line endpoint or another line', next.client)
          return
        }
        this.#options.commit(preview.source, preview.target, next.client)
      },
      cancel: () => { this.#preview = null },
    }
  }

  overlay(): readonly Shape[] {
    const preview = this.#preview
    if (preview === null) return []
    const color = this.#options.theme().interaction.valid
    const out: Shape[] = [{ kind: 'segment', from: preview.from, to: preview.at, stroke: color, width: 1.6, glow: null }]
    if (preview.target !== null) out.push(...targetShapes(this.#options.engine(), preview.target, color, 3.2))
    return out
  }

  cancel(): void { this.#preview = null }
}
