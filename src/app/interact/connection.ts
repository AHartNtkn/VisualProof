import type { Endpoint, NodeId, WireId } from '../../kernel/diagram/diagram'
import { pkey, type Engine } from '../../view/engine'
import type { Shape, Theme } from '../../view/paint'
import { wireOverlayShapes } from '../../view/paint'
import type { Vec2 } from '../../view/vec'
import {
  type WireManipulationHit,
  wireManipulationHitTest,
} from '../hittest'
import type { PointerClaim, PointerSample } from './viewport'

export type ConnectionEnd = {
  readonly wire: WireId
  readonly endpoint: Endpoint | null
}

/** A connection's drop target: a wire (its own end or strand) or, when the
    host supplies `identityTarget`, an identity dot — ports are not things
    a gesture can name, so a dot target names the node, never a leg. */
export type ConnectionTarget = ConnectionEnd | { readonly identity: NodeId }

/** The wire-to-wire (or wire-to-dot) connection: the merge gesture. */
export type ConnectionGesture = {
  readonly source: ConnectionEnd
  readonly target: ConnectionTarget
}

export type ConnectionDragOptions = {
  readonly active: () => boolean
  readonly engine: () => Engine
  readonly viewScale: () => number
  readonly theme: () => Theme
  readonly commit: (gesture: ConnectionGesture, pointer: Vec2) => boolean
  readonly refuse: (text: string, pointer: Vec2) => void
  /** Limit which physical source ends this controller owns. */
  readonly acceptSource?: (source: ConnectionEnd) => boolean
  /** Identity dot under a point, when the host wants dot drops recognized
      (construction mode; proving mode passes nothing and sees no change). */
  readonly identityTarget?: (point: Vec2) => NodeId | null
}

type WirePreview = {
  readonly source: ConnectionEnd
  readonly from: Vec2
  at: Vec2
  target: ConnectionTarget | null
}

function wireEnd(hit: WireManipulationHit): ConnectionEnd {
  return {
    wire: hit.wire,
    endpoint: hit.kind === 'endpoint' ? hit.endpoint : null,
  }
}

function wireTargetShapes(
  engine: Engine,
  target: ConnectionEnd,
  stroke: string,
  width: number,
): Shape[] {
  if (target.endpoint === null) return wireOverlayShapes(engine, target.wire, stroke, width)
  // endpoint-scoped feedback restrokes only the legs at that port
  const key = pkey(target.endpoint.port)
  return wireOverlayShapes(engine, target.wire, stroke, width, null, (leg) =>
    (leg.from.body === target.endpoint!.node && leg.from.key === key)
    || (leg.to.body === target.endpoint!.node && leg.to.key === key))
}

/** The wire-to-wire connection drag, shared by construction and proving. */
export class ConnectionDragController {
  readonly #options: ConnectionDragOptions
  #preview: WirePreview | null = null
  #claimEpoch = 0

  constructor(options: ConnectionDragOptions) {
    this.#options = options
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
    const source = wireEnd(hit)
    if (this.#options.acceptSource?.(source) === false) return null
    const preview: WirePreview = {
      source,
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
        preview.target = this.#targetAt(next.world)
      },
      release: (next, moved) => {
        this.#preview = null
        if (!moved) return
        const target = this.#targetAt(next.world)
        if (target === null) {
          this.#options.refuse(
            'release on a line endpoint or another line',
            next.client,
          )
          return
        }
        this.#options.commit({
          source: preview.source,
          target,
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
      if ('identity' in preview.target) {
        const body = engine.bodies.get(preview.target.identity)
        if (body !== undefined) {
          out.push({
            kind: 'circle',
            center: body.pos,
            r: body.discR * engine.scale + 1.5,
            fill: null,
            stroke: color,
            width: 2,
            insetColor: null,
            glow: null,
          })
        }
      } else {
        out.push(...wireTargetShapes(engine, preview.target, color, 3.2))
      }
    }
    return out
  }

  cancel(): void {
    this.#claimEpoch++
    this.#preview = null
  }

  /** The identity dot under the point resolves before the wire hit-test —
      the same discs-outrank-terminals precedent wire-ops.ts and
      identity-ops.ts's own dot-drop dispatch already follow. Identity
      ports anchor at their dot's exact centre (the rendering law: "the
      point IS the drawing"), so every wire attached to a dot has its own
      terminal sitting there too; checking the wire hit first would let a
      drop anywhere in a multi-wire dot's disc resolve to whichever
      attached wire's terminal happens to win a distance-0 tie, silently
      committing fission (or a misleading same-wire refusal) instead of
      the intended duplicate. */
  #targetAt(point: Vec2): ConnectionTarget | null {
    const dot = this.#options.identityTarget?.(point) ?? null
    if (dot !== null) return { identity: dot }
    const hit = wireManipulationHitTest(
      this.#options.engine(),
      point,
      { scale: this.#options.viewScale() },
    )
    return hit === null ? null : wireEnd(hit)
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
