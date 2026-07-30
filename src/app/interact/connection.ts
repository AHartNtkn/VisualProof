import type { Endpoint, WireId } from '../../kernel/diagram/diagram'
import { pkey, type Engine } from '../../view/engine'
import type { Shape, Theme } from '../../view/paint'
import type { Vec2 } from '../../view/vec'
import { computeLegs, existentialStubs, legPaths } from '../../view/wires'
import {
  type WireManipulationHit,
  wireManipulationHitTest,
} from '../hittest'
import type { PointerClaim, PointerSample } from './viewport'

export type ConnectionEnd = {
  readonly wire: WireId
  readonly endpoint: Endpoint | null
}

/** The wire-to-wire connection: the merge gesture. */
export type ConnectionGesture = {
  readonly source: ConnectionEnd
  readonly target: ConnectionEnd
}

export type ConnectionDragOptions = {
  readonly active: () => boolean
  readonly engine: () => Engine
  readonly viewScale: () => number
  readonly theme: () => Theme
  readonly commit: (gesture: ConnectionGesture, pointer: Vec2) => boolean
  readonly refuse: (text: string, pointer: Vec2) => void
}

type WirePreview = {
  readonly source: ConnectionEnd
  readonly from: Vec2
  at: Vec2
  target: ConnectionEnd | null
}

function wireEnd(hit: WireManipulationHit): ConnectionEnd {
  return {
    wire: hit.wire,
    endpoint: hit.kind === 'endpoint' ? hit.endpoint : null,
  }
}

function wireShapes(engine: Engine, wire: WireId, stroke: string, width: number): Shape[] {
  const out: Shape[] = []
  for (const path of legPaths(engine)) {
    if (path.wid === wire) {
      out.push({ kind: 'polyline', pts: path.pts, stroke, width, glow: null })
    }
  }
  for (const stub of existentialStubs(engine)) {
    if (stub.wid === wire) {
      out.push({
        kind: 'segment',
        from: stub.from,
        to: stub.to,
        stroke,
        width,
        glow: null,
      })
    }
  }
  return out
}

function wireTargetShapes(
  engine: Engine,
  target: ConnectionEnd,
  stroke: string,
  width: number,
): Shape[] {
  if (target.endpoint === null) return wireShapes(engine, target.wire, stroke, width)
  const key = pkey(target.endpoint.port)
  return computeLegs(engine)
    .filter(({ leg }) => leg.wid === target.wire && (
      (leg.from.body === target.endpoint!.node && leg.from.key === key)
      || (leg.to.body === target.endpoint!.node && leg.to.key === key)
    ))
    .map(({ pts }): Shape => ({
      kind: 'polyline',
      pts,
      stroke,
      width,
      glow: null,
    }))
}

/** The wire-to-wire connection drag, shared by construction and proving. */
export class ConnectionDragController {
  readonly #options: ConnectionDragOptions
  #preview: WirePreview | null = null
  #claimEpoch = 0

  constructor(options: ConnectionDragOptions) {
    this.#options = options
  }

  get hasPendingInteraction(): boolean {
    return this.#preview !== null
  }

  claim(sample: PointerSample): PointerClaim | null {
    if (
      !this.#options.active()
      || sample.button !== 0
      || sample.shiftKey
      || sample.ctrlKey
    ) return null
    const viewport = { scale: this.#options.viewScale() }
    const hit = wireManipulationHitTest(
      this.#options.engine(),
      sample.world,
      viewport,
    )
    if (hit === null) return null
    const preview: WirePreview = {
      source: wireEnd(hit),
      from: sample.world,
      at: sample.world,
      target: null,
    }
    this.#preview = preview
    return this.#issueClaim({
      still: 'selection',
      blocksPassiveRelaxation: true,
      move: (next) => {
        preview.at = next.world
        const target = wireManipulationHitTest(
          this.#options.engine(),
          next.world,
          { scale: this.#options.viewScale() },
        )
        preview.target = target === null ? null : wireEnd(target)
      },
      release: (next, moved) => {
        this.#preview = null
        if (!moved) return
        const target = wireManipulationHitTest(
          this.#options.engine(),
          next.world,
          { scale: this.#options.viewScale() },
        )
        if (target === null) {
          this.#options.refuse(
            'release on a line endpoint or another line',
            next.client,
          )
          return
        }
        this.#options.commit({
          source: preview.source,
          target: wireEnd(target),
        }, next.client)
      },
      cancel: () => {
        this.#preview = null
      },
    })
  }

  overlay(): readonly Shape[] {
    const engine = this.#options.engine()
    const color = this.#options.theme().interaction.valid
    const out: Shape[] = []
    const preview = this.#preview
    if (preview === null) return out
    out.push({
      kind: 'segment',
      from: preview.from,
      to: preview.at,
      stroke: color,
      width: 1.6,
      glow: null,
    })
    if (preview.target !== null) {
      out.push(...wireTargetShapes(engine, preview.target, color, 3.2))
    }
    return out
  }

  cancel(): void {
    this.#claimEpoch++
    this.#preview = null
  }

  #issueClaim(claim: PointerClaim): PointerClaim {
    const epoch = ++this.#claimEpoch
    const current = (): boolean => this.#claimEpoch === epoch
    const retire = (): boolean => {
      if (!current()) return false
      this.#claimEpoch++
      return true
    }
    return {
      still: claim.still,
      blocksPassiveRelaxation: claim.blocksPassiveRelaxation,
      ...(claim.relaxationPins === undefined ? {} : {
        relaxationPins: (): readonly string[] =>
          current() ? claim.relaxationPins!() : [],
      }),
      move: (sample) => {
        if (current()) claim.move(sample)
      },
      release: (sample, moved) => {
        if (retire()) claim.release(sample, moved)
      },
      cancel: () => {
        if (retire()) claim.cancel()
      },
    }
  }
}
