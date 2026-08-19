import type { Diagram, Endpoint, WireId } from '../../kernel/diagram/diagram'
import { pkey, type Engine, type Leg } from '../../view/engine'
import type { Shape, Theme } from '../../view/paint'
import type { Vec2 } from '../../view/vec'
import { computeLegs, type LegGeom } from '../../view/wires'
import type { PointerClaim, PointerSample } from './viewport'

export type SlashCrossing = { readonly wire: WireId; readonly endpoint: Endpoint }

export type SlashOptions = {
  readonly active: () => boolean
  readonly engine: () => Engine
  readonly diagram: () => Diagram
  readonly theme: () => Theme
  /** Endpoint-resolved crossings, at least one. Junction-only legs are pre-filtered. */
  readonly commit: (crossings: readonly SlashCrossing[], sample: PointerSample) => void
  /** A still right-click: the mode's resting right-click surface (spawn / context). */
  readonly still: (sample: PointerSample) => void
  readonly refuse: (text: string, pointer: Vec2) => void
}

function crosses(a: Vec2, b: Vec2, c: Vec2, d: Vec2): boolean {
  const orient = (p: Vec2, q: Vec2, r: Vec2): number => (q.x - p.x) * (r.y - p.y) - (q.y - p.y) * (r.x - p.x)
  const abC = orient(a, b, c)
  const abD = orient(a, b, d)
  const cdA = orient(c, d, a)
  const cdB = orient(c, d, b)
  const overlaps = (a0: number, a1: number, b0: number, b1: number): boolean =>
    Math.max(Math.min(a0, a1), Math.min(b0, b1)) <= Math.min(Math.max(a0, a1), Math.max(b0, b1))
  return abC * abD <= 0 && cdA * cdB <= 0
    && overlaps(a.x, b.x, c.x, d.x)
    && overlaps(a.y, b.y, c.y, d.y)
}

function crossedLegs(engine: Engine, from: Vec2, to: Vec2): LegGeom[] {
  return computeLegs(engine).filter((geometry) => {
    for (let i = 1; i < geometry.pts.length; i++) {
      if (crosses(from, to, geometry.pts[i - 1]!, geometry.pts[i]!)) return true
    }
    return false
  })
}

function endpointAt(diagram: Diagram, leg: Leg): Endpoint | null {
  for (const end of [leg.to, leg.from]) {
    if (diagram.nodes[end.body] === undefined) continue
    const endpoint = diagram.wires[leg.wid]?.endpoints.find((candidate) =>
      candidate.node === end.body && pkey(candidate.port) === end.key)
    if (endpoint !== undefined) return endpoint
  }
  return null
}

/**
 * The slash: a right-drag straight line that severs every wire leg it
 * crosses. A still right-click reaches the mode's resting right-click
 * surface instead.
 */
export class SlashController {
  readonly #options: SlashOptions
  #preview: { readonly from: Vec2; at: Vec2 } | null = null
  #suppressMenu = false

  constructor(options: SlashOptions) {
    this.#options = options
  }

  /** True exactly once after a claimed right release, to suppress the browser contextmenu. */
  consumeMenuSuppression(): boolean {
    const suppressed = this.#suppressMenu
    this.#suppressMenu = false
    return suppressed
  }

  overlay(): readonly Shape[] {
    const preview = this.#preview
    if (preview === null) return []
    return [{
      kind: 'segment',
      from: preview.from,
      to: preview.at,
      stroke: this.#options.theme().interaction.refusal,
      width: 2,
      glow: null,
    }]
  }

  cancel(): void {
    this.#preview = null
  }

  claim(start: PointerSample): PointerClaim | null {
    if (!this.#options.active() || start.button !== 2) return null
    const preview = { from: start.world, at: start.world }
    this.#preview = preview
    this.#suppressMenu = true
    return {
      still: 'claim',
      blocksPassiveRelaxation: true,
      move: (sample) => { preview.at = sample.world },
      release: (sample, moved) => {
        this.#preview = null
        if (!moved) {
          this.#options.still(start)
          return
        }
        const legs = crossedLegs(this.#options.engine(), preview.from, sample.world)
        if (legs.length === 0) {
          this.#options.refuse('the slash crossed no strand', sample.client)
          return
        }
        const diagram = this.#options.diagram()
        const crossings: SlashCrossing[] = []
        let junctionOnly = false
        for (const geometry of legs) {
          const endpoint = endpointAt(diagram, geometry.leg)
          if (endpoint === null) { junctionOnly = true; continue }
          crossings.push({ wire: geometry.leg.wid, endpoint })
        }
        if (crossings.length > 0) {
          this.#options.commit(crossings, sample)
        } else if (junctionOnly) {
          this.#options.refuse('that strand runs between junctions; sever nearer a port', sample.client)
        }
      },
      cancel: () => { this.#preview = null },
    }
  }
}
