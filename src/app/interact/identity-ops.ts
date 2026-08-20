import type { Diagram, IdentityDiagramNode, NodeId, WireId } from '../../kernel/diagram/diagram'
import { isAncestorOrEqual } from '../../kernel/diagram/regions'
import {
  applyIdentification,
  applyPresentation,
  applyVacuityDelete,
  applyVacuityInsert,
} from '../../kernel/rules/identity-rules'
import { RuleError } from '../../kernel/rules/error'
import type { ProofStep } from '../../kernel/proof/step'
import type { Engine } from '../../view/engine'
import type { Shape, Theme } from '../../view/paint'
import { length, sub } from '../../view/vec'
import type { Vec2 } from '../../view/vec'
import { regionAt, wireManipulationHitTest } from '../hittest'
import { headWireOf } from './wire-ops'
import type { PointerClaim, PointerSample } from './viewport'

/** What a press grabbed, in identity-rule vocabulary. */
export type IdentityGrab =
  | { readonly kind: 'dot'; readonly node: NodeId }
  | { readonly kind: 'dotRim'; readonly node: NodeId }
  | { readonly kind: 'leg'; readonly node: NodeId; readonly wire: WireId; readonly index: number }
  | { readonly kind: 'endDisc'; readonly node: NodeId; readonly wire: WireId }

export type IdentityOpsOptions = {
  readonly active: () => boolean
  readonly engine: () => Engine
  readonly diagram: () => Diagram
  readonly viewScale: () => number
  readonly theme: () => Theme
  /** Edit mode claims atom/ref end discs for the expose drag; proof mode
      leaves them to WireOpsDragController, which owns richer end drops. */
  readonly claimEndDiscs: boolean
  readonly commit: (label: string, steps: readonly ProofStep[], pointer: Vec2) => boolean
  readonly refuse: (text: string, pointer: Vec2) => void
}

const HIT_RADIUS_PX = 6

/** The identity dot whose disc (interior or rim halo) contains the point. */
export function identityDiscAt(engine: Engine, point: Vec2): NodeId | null {
  for (const body of engine.bodies.values()) {
    if (body.kind !== 'identity') continue
    const distance = length(sub(point, body.pos))
    if (distance <= body.discR * engine.scale) return body.id
  }
  return null
}

/** Edit-mode committer: apply identity-rule steps directly (they are ungated). */
export function applyIdentitySteps(d: Diagram, steps: readonly ProofStep[]): Diagram {
  let next = d
  for (const step of steps) {
    switch (step.rule) {
      case 'vacuity':
        next = step.direction === 'insert'
          ? applyVacuityInsert(next, step.instance)
          : applyVacuityDelete(next, step.instance)
        break
      case 'presentation':
        next = applyPresentation(next, step.input)
        break
      case 'identification':
        next = applyIdentification(next, step.input)
        break
      default:
        throw new Error(`'${step.rule}' is not an identity-rule step`)
    }
  }
  return next
}

/** Collapse at `node`: absorb all its wires into a survivor. Throws RuleError
    when the dot has fewer than two distinct wires. */
export function collapseStep(d: Diagram, node: NodeId): ProofStep {
  const dot = d.nodes[node]
  if (dot === undefined || dot.kind !== 'identity') throw new RuleError(`'${node}' is not an identity node`)
  const attached = [...new Set(
    Object.entries(d.wires)
      .filter(([, w]) => w.endpoints.some((ep) => ep.node === node))
      .map(([id]) => id),
  )].sort()
  if (attached.length < 2) {
    throw new RuleError(`collapse needs at least two wires at '${node}'`)
  }
  const violates = (wireId: WireId): boolean =>
    d.wires[wireId]!.endpoints.some((ep) =>
      ep.node !== node && !isAncestorOrEqual(d, dot.region, d.nodes[ep.node]!.region))
  const violators = attached.filter(violates)
  const survivor = violators[0] ?? attached[0]!
  return {
    rule: 'identification',
    input: { kind: 'collapse', node, survivor, absorbed: attached.filter((w) => w !== survivor) },
  }
}

/** `node`'s identity-port wires, ordered by port index (one entry per port —
    multiplicity preserved when a wire occupies more than one of its ports). */
function portWires(d: Diagram, node: NodeId): WireId[] {
  const out: [number, WireId][] = []
  for (const [wireId, wire] of Object.entries(d.wires)) {
    for (const ep of wire.endpoints) {
      if (ep.node === node && ep.port.kind === 'identity') out.push([ep.port.index, wireId])
    }
  }
  return out.sort(([i], [j]) => i - j).map(([, w]) => w)
}

/** Fuse `a` and `b` into a single identity node presenting the union of
    their ports — presentation invariance, so the kernel is the sole
    authority on the region/sig match. */
export function fuseStep(d: Diagram, a: NodeId, b: NodeId): ProofStep {
  const region = (d.nodes[a] as IdentityDiagramNode).region
  return {
    rule: 'presentation',
    input: {
      region,
      removeNodes: [a, b],
      addNodes: { dot: [...portWires(d, a), ...portWires(d, b)] },
    },
  }
}

/**
 * The shared identity-rule gesture surface: grabs on an identity dot, its
 * rim, an attached leg, or (edit mode) an atom/ref end disc, dispatched by
 * object kind exactly as WireOpsDragController dispatches wire grabs. This
 * task implements the dot-into-open-space collapse row and the
 * dot-onto-dot fuse row; the remaining rows refuse with placeholder-free
 * messages naming their gesture until later tasks land them.
 */
export class IdentityOpsController {
  readonly #options: IdentityOpsOptions
  #drag: { readonly grab: IdentityGrab; readonly from: Vec2; at: Vec2 } | null = null
  #claimEpoch = 0

  constructor(options: IdentityOpsOptions) {
    this.#options = options
  }

  claim(sample: PointerSample): PointerClaim | null {
    if (
      !this.#options.active()
      || sample.button !== 0
      || sample.shiftKey
      || sample.ctrlKey
    ) return null
    const grab = this.#grabAt(sample.world)
    if (grab === null) return null
    const drag = { grab, from: sample.world, at: sample.world }
    this.#drag = drag
    return this.#issueClaim({
      still: 'selection',
      blocksPassiveRelaxation: true,
      move: (next) => {
        drag.at = next.world
      },
      release: (next, moved) => {
        this.#drag = null
        if (!moved) return
        this.#drop(grab, next)
      },
      cancel: () => {
        this.#drag = null
      },
    })
  }

  overlay(): readonly Shape[] {
    const drag = this.#drag
    if (drag === null) return []
    const color = this.#options.theme().interaction.valid
    return [{
      kind: 'segment',
      from: drag.from,
      to: drag.at,
      stroke: color,
      width: 1.6,
      glow: null,
    }]
  }

  cancel(): void {
    this.#claimEpoch++
    this.#drag = null
  }

  #radius(): number {
    return HIT_RADIUS_PX / this.#options.viewScale()
  }

  #grabAt(point: Vec2): IdentityGrab | null {
    const engine = this.#options.engine()
    const halo = this.#radius()
    for (const body of engine.bodies.values()) {
      if (body.kind !== 'identity') continue
      const r = body.discR * engine.scale
      const distance = length(sub(point, body.pos))
      if (Math.abs(distance - r) <= halo) return { kind: 'dotRim', node: body.id }
      if (distance < r - halo) return { kind: 'dot', node: body.id }
    }
    const viewport = { scale: this.#options.viewScale() }
    const manipulation = wireManipulationHitTest(engine, point, viewport)
    if (manipulation !== null && manipulation.kind === 'endpoint' && manipulation.endpoint.port.kind === 'identity') {
      return {
        kind: 'leg',
        node: manipulation.endpoint.node,
        wire: manipulation.wire,
        index: manipulation.endpoint.port.index,
      }
    }
    if (this.#options.claimEndDiscs) {
      const endDisc = this.#endDiscAt(point)
      if (endDisc !== null) return { kind: 'endDisc', node: endDisc.node, wire: endDisc.wire }
    }
    return null
  }

  #drop(grab: IdentityGrab, sample: PointerSample): void {
    const engine = this.#options.engine()
    const diagram = this.#options.diagram()
    const viewport = { scale: this.#options.viewScale() }
    const point = sample.world
    switch (grab.kind) {
      case 'dot': {
        const target = identityDiscAt(engine, point)
        if (target !== null && target !== grab.node) {
          this.#options.commit('presentation', [fuseStep(diagram, grab.node, target)], sample.client)
          return
        }
        if (!this.#isOpenSpace(point, viewport) || target !== null) {
          this.#options.refuse(
            'release in open space to collapse, or on another dot to fuse',
            sample.client,
          )
          return
        }
        try {
          const step = collapseStep(diagram, grab.node)
          this.#options.commit('identification', [step], sample.client)
        } catch (error) {
          this.#options.refuse(
            error instanceof Error ? error.message : String(error),
            sample.client,
          )
        }
        return
      }
      case 'dotRim': {
        if (!this.#isOpenSpace(point, viewport)) {
          this.#options.refuse('pull the stub into open space', sample.client)
          return
        }
        const dropRegion = regionAt(engine, diagram, point)
        const step: ProofStep = {
          rule: 'vacuity',
          direction: 'insert',
          instance: { kind: 'stub', base: grab.node, wire: 'w', end: 'w_end', region: dropRegion },
        }
        this.#options.commit('vacuity', [step], sample.client)
        return
      }
      case 'leg': {
        this.#options.refuse('release on the dot or one of its legs', sample.client)
        return
      }
      case 'endDisc': {
        this.#options.refuse('release on an identity dot on this wire to expose', sample.client)
        return
      }
    }
  }

  /** No wire-manipulation hit, no identity disc, no end disc — the point a
      dot (or its rim) may be dropped onto to grow or collapse. */
  #isOpenSpace(point: Vec2, viewport: { readonly scale: number }): boolean {
    const engine = this.#options.engine()
    if (wireManipulationHitTest(engine, point, viewport) !== null) return false
    if (identityDiscAt(engine, point) !== null) return false
    if (this.#options.claimEndDiscs && this.#endDiscAt(point) !== null) return false
    return true
  }

  #endDiscAt(point: Vec2): { readonly node: NodeId; readonly wire: WireId } | null {
    const engine = this.#options.engine()
    const diagram = this.#options.diagram()
    for (const body of engine.bodies.values()) {
      if (body.kind !== 'atom' && body.kind !== 'ref') continue
      const radius = body.discR * engine.scale
      if (length(sub(point, body.pos)) > radius) continue
      const wire = headWireOf(diagram, body.id)
      if (wire === null) continue
      return { node: body.id, wire }
    }
    return null
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
