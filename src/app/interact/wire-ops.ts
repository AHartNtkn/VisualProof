import type {
  Diagram,
  NodeId,
  RegionId,
  WireId,
} from '../../kernel/diagram/diagram'
import type { Sig } from '../../kernel/diagram/sig'
import type { ProofContext } from '../../kernel/proof/context'
import { applyStep, type ProofStep } from '../../kernel/proof/step'
import { pkey, type Engine } from '../../view/engine'
import type { Shape, Theme } from '../../view/paint'
import { computeLegs } from '../../view/wires'
import { length, sub } from '../../view/vec'
import type { Vec2 } from '../../view/vec'
import { wireManipulationHitTest } from '../hittest'
import { duplicateStep, exposeStep, fissionStep, identityDiscAt, sharedDots } from './identity-ops'
import type { PointerClaim, PointerSample } from './viewport'

/** What a press grabbed, in the object vocabulary of the drag table. */
type Grab =
  | { readonly kind: 'port'; readonly node: NodeId; readonly wire: WireId; readonly position: number }
  | { readonly kind: 'end'; readonly node: NodeId; readonly wire: WireId }
  | { readonly kind: 'rim'; readonly node: NodeId; readonly wire: WireId }
  | { readonly kind: 'strand'; readonly wire: WireId }
  | { readonly kind: 'cutRing'; readonly region: RegionId }

export type WireOpsOptions = {
  readonly active: () => boolean
  readonly engine: () => Engine
  readonly diagram: () => Diagram
  readonly viewScale: () => number
  readonly theme: () => Theme
  readonly context: () => ProofContext
  readonly orientation: () => 'forward' | 'backward'
  /** Commit one atomic action; false means the kernel refused it. */
  readonly commit: (
    label: string,
    steps: readonly ProofStep[],
    pointer: Vec2,
  ) => boolean
  /** Ask for the new position's signature (the arity prompt), then apply. */
  readonly promptSig: (client: Vec2, apply: (sig: Sig) => void) => void
  readonly refuse: (text: string, pointer: Vec2) => void
}

const HIT_RADIUS_PX = 6

/** The wire a node is an applied end of, i.e. holding its head port. */
export function headWireOf(diagram: Diagram, node: NodeId): WireId | null {
  for (const [wireId, wire] of Object.entries(diagram.wires)) {
    if (wire.endpoints.some((endpoint) =>
      endpoint.node === node && endpoint.port.kind === 'head')) return wireId
  }
  return null
}

/** The wire attached to `node`'s argument port at `position` — the actual
    wire an argument-port grab manipulates, as opposed to `grab.wire`
    (the node's own head wire, used by the arity-editing rows). */
function argWireOf(diagram: Diagram, node: NodeId, position: number): WireId | null {
  for (const [wireId, wire] of Object.entries(diagram.wires)) {
    if (wire.endpoints.some((endpoint) =>
      endpoint.node === node && endpoint.port.kind === 'arg' && endpoint.port.index === position)) return wireId
  }
  return null
}

/** Every applied-end node of a wire. */
function appliedEndNodes(diagram: Diagram, wire: WireId): readonly NodeId[] {
  return (diagram.wires[wire]?.endpoints ?? [])
    .filter((endpoint) => endpoint.port.kind === 'head')
    .map((endpoint) => endpoint.node)
}

/**
 * The instantiation-direction drags: what a gesture means is fixed by which
 * objects it grabs and drops on — wire strand, end node, end rim, argument
 * port, cut ring — never by selection or menus. Each row commits one
 * primitive acting uniformly on all ends of the demonstrated wire; a failed
 * gate refuses by spring-back at commit.
 */
export class WireOpsDragController {
  readonly #options: WireOpsOptions
  #drag: { readonly grab: Grab; readonly from: Vec2; at: Vec2 } | null = null
  #claimEpoch = 0

  constructor(options: WireOpsOptions) {
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
    const engine = this.#options.engine()
    const diagram = this.#options.diagram()
    const color = this.#options.theme().interaction.valid
    const out: Shape[] = [{
      kind: 'segment',
      from: drag.from,
      to: drag.at,
      stroke: color,
      width: 1.6,
      glow: null,
    }]
    // One-site demonstration: every end the committed step will transform
    // stays highlighted while one of them is being demonstrated on.
    const wire = drag.grab.kind === 'cutRing' ? null : drag.grab.wire
    if (wire !== null) {
      for (const node of appliedEndNodes(diagram, wire)) {
        const body = engine.bodies.get(node)
        if (body === undefined) continue
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
    }
    return out
  }

  cancel(): void {
    this.#claimEpoch++
    this.#drag = null
  }

  #radius(): number {
    return HIT_RADIUS_PX / this.#options.viewScale()
  }

  /** The atom/ref disc containing the point, with its applied head wire. */
  #discAt(point: Vec2): { readonly node: NodeId; readonly wire: WireId; readonly center: Vec2; readonly radius: number } | null {
    const engine = this.#options.engine()
    const diagram = this.#options.diagram()
    for (const body of engine.bodies.values()) {
      if (body.kind !== 'atom' && body.kind !== 'ref') continue
      const radius = body.discR * engine.scale
      if (length(sub(point, body.pos)) > radius) continue
      const wire = headWireOf(diagram, body.id)
      if (wire === null) continue
      return { node: body.id, wire, center: body.pos, radius }
    }
    return null
  }

  #grabAt(point: Vec2): Grab | null {
    const engine = this.#options.engine()
    const diagram = this.#options.diagram()
    const viewport = { scale: this.#options.viewScale() }
    const manipulation = wireManipulationHitTest(engine, point, viewport)
    if (manipulation !== null) {
      if (manipulation.kind === 'endpoint') {
        const { node, port } = manipulation.endpoint
        if (port.kind === 'arg') {
          const wire = headWireOf(diagram, node)
          if (wire !== null) {
            return { kind: 'port', node, wire, position: port.index }
          }
        }
        if (port.kind === 'head') {
          return { kind: 'rim', node, wire: manipulation.wire }
        }
      }
      return { kind: 'strand', wire: manipulation.wire }
    }
    const disc = this.#discAt(point)
    if (disc !== null) {
      const onRim =
        Math.abs(length(sub(point, disc.center)) - disc.radius) <= this.#radius()
      return onRim
        ? { kind: 'rim', node: disc.node, wire: disc.wire }
        : { kind: 'end', node: disc.node, wire: disc.wire }
    }
    for (const [region, geometry] of engine.regions) {
      if (this.#options.diagram().regions[region]?.kind === 'sheet') continue
      const ringDistance =
        Math.abs(length(sub(point, geometry.center)) - geometry.radius)
      if (ringDistance <= this.#radius()) return { kind: 'cutRing', region }
    }
    return null
  }

  /** World anchor of one argument position on an applied end. */
  #argAnchor(node: NodeId, position: number): Vec2 | null {
    const engine = this.#options.engine()
    const key = pkey({ kind: 'arg', index: position })
    for (const geometry of computeLegs(engine)) {
      if (geometry.pts.length === 0) continue
      if (geometry.leg.from.body === node && geometry.leg.from.key === key) {
        return geometry.pts[0]!
      }
      if (geometry.leg.to.body === node && geometry.leg.to.key === key) {
        return geometry.pts.at(-1)!
      }
    }
    return null
  }

  #commit(label: string, step: ProofStep, sample: PointerSample): void {
    this.#options.commit(label, [step], sample.client)
  }

  #drop(grab: Grab, sample: PointerSample): void {
    const engine = this.#options.engine()
    const diagram = this.#options.diagram()
    const viewport = { scale: this.#options.viewScale() }
    const point = sample.world
    switch (grab.kind) {
      case 'strand': {
        const dot = identityDiscAt(engine, point)
        if (dot !== null) {
          if (diagram.wires[grab.wire]!.endpoints.some((ep) => ep.node === dot)) {
            this.#commit('presentation', duplicateStep(diagram, dot, grab.wire), sample)
            return
          }
          this.#options.refuse('this line is not attached to that dot', sample.client)
          return
        }
        const disc = this.#discAt(point)
        if (disc !== null) {
          if (disc.wire === grab.wire) {
            this.#options.refuse(
              'a wire cannot become its own new argument',
              sample.client,
            )
            return
          }
          const target = diagram.wires[disc.wire]!
          if (target.sig.kind !== 'rel') return
          const attachments = Object.fromEntries(
            appliedEndNodes(diagram, disc.wire)
              .map((node) => [node, grab.wire]),
          )
          this.#commit('argExtend', {
            rule: 'argExtend',
            wire: disc.wire,
            position: target.sig.args.length,
            newArgSig: diagram.wires[grab.wire]!.sig,
            attachments,
          }, sample)
          return
        }
        const manipulation = wireManipulationHitTest(engine, point, viewport)
        if (manipulation === null) {
          this.#options.refuse(
            'release on a line or an end',
            sample.client,
          )
          return
        }
        if (manipulation.wire === grab.wire) {
          this.#options.refuse(
            `line '${manipulation.wire}' is already one identity`,
            sample.client,
          )
          return
        }
        const shared = sharedDots(diagram, grab.wire, manipulation.wire)
        if (shared.length > 1) {
          this.#options.refuse('these lines meet at several dots', sample.client)
          return
        }
        if (shared.length === 1) {
          this.#commit('presentation', fissionStep(diagram, shared[0]!, grab.wire, manipulation.wire), sample)
          return
        }
        this.#commit('wireJoin', {
          rule: 'wireJoin',
          input: { a: grab.wire, b: manipulation.wire },
        }, sample)
        return
      }
      case 'end': {
        const manipulation = wireManipulationHitTest(engine, point, viewport)
        if (
          manipulation?.kind === 'endpoint'
          && manipulation.endpoint.node === grab.node
          && manipulation.endpoint.port.kind === 'arg'
        ) {
          this.#commit('identityLeaf', {
            rule: 'identityLeaf',
            wire: grab.wire,
          }, sample)
          return
        }
        const disc = this.#discAt(point)
        if (disc !== null && disc.node !== grab.node) {
          if (disc.wire === grab.wire) {
            this.#options.refuse(
              'these are already ends of one wire',
              sample.client,
            )
            return
          }
          const [a, b] = [grab.wire, disc.wire].sort() as [WireId, WireId]
          this.#commit('parallelFuse', { rule: 'parallelFuse', a, b }, sample)
          return
        }
        if (disc === null && manipulation === null) {
          this.#commit('parallelSplit', {
            rule: 'parallelSplit',
            wire: grab.wire,
          }, sample)
          return
        }
        const dot = identityDiscAt(engine, point)
        if (dot !== null && diagram.wires[grab.wire]!.endpoints.some((ep) => ep.node === dot)) {
          this.#commit(
            'identification',
            exposeStep(diagram, dot, grab.wire, { node: grab.node, port: { kind: 'head' } }),
            sample,
          )
          return
        }
        this.#options.refuse(
          'release on a parallel end, an own argument port, an identity dot on this wire, or open space',
          sample.client,
        )
        return
      }
      case 'rim': {
        const manipulation = wireManipulationHitTest(engine, point, viewport)
        if (manipulation !== null || this.#discAt(point) !== null) {
          this.#options.refuse(
            'pull the new argument stub into open space',
            sample.client,
          )
          return
        }
        const wire = grab.wire
        this.#options.promptSig(sample.client, (sig) => {
          this.#commit('arityShift', {
            rule: 'arityShift',
            wire,
            newArgSig: sig,
          }, sample)
        })
        return
      }
      case 'port': {
        const manipulation = wireManipulationHitTest(engine, point, viewport)
        if (
          manipulation?.kind === 'endpoint'
          && manipulation.endpoint.node === grab.node
          && manipulation.endpoint.port.kind === 'arg'
        ) {
          const target = manipulation.endpoint.port.index
          if (target === grab.position) return
          if (target === grab.position + 1 || target === grab.position - 1) {
            this.#commit('argContract', {
              rule: 'argContract',
              wire: grab.wire,
              position: Math.min(grab.position, target),
            }, sample)
            return
          }
          this.#options.refuse(
            'only adjacent argument positions contract',
            sample.client,
          )
          return
        }
        const body = engine.bodies.get(grab.node)
        const discRadius = body === undefined
          ? 0
          : body.discR * engine.scale
        if (body !== undefined && length(sub(point, body.pos)) <= discRadius) {
          if (length(sub(point, body.pos)) <= discRadius / 2) {
            this.#commit('applyFormal', {
              rule: 'applyFormal',
              wire: grab.wire,
              position: grab.position,
            }, sample)
            return
          }
          const arity = this.#arity(diagram, grab.wire)
          let nearest: { position: number; distance: number } | null = null
          for (let index = 0; index < arity; index += 1) {
            const anchor = this.#argAnchor(grab.node, index)
            if (anchor === null) continue
            const distance = length(sub(point, anchor))
            if (nearest === null || distance < nearest.distance) {
              nearest = { position: index, distance }
            }
          }
          if (nearest === null) return
          if (nearest.position === grab.position) {
            this.#commit('argDuplicate', {
              rule: 'argDuplicate',
              wire: grab.wire,
              position: grab.position,
            }, sample)
            return
          }
          const permutation = Array.from({ length: arity }, (_, i) => i)
          permutation[grab.position] = nearest.position
          permutation[nearest.position] = grab.position
          this.#commit('argPermute', {
            rule: 'argPermute',
            wire: grab.wire,
            permutation,
          }, sample)
          return
        }
        const dot = identityDiscAt(engine, point)
        if (dot !== null) {
          const argWire = argWireOf(diagram, grab.node, grab.position)
          if (argWire !== null && diagram.wires[argWire]!.endpoints.some((ep) => ep.node === dot)) {
            this.#commit(
              'identification',
              exposeStep(diagram, dot, argWire, { node: grab.node, port: { kind: 'arg', index: grab.position } }),
              sample,
            )
            return
          }
        }
        // Off the node: remove the position. Unshift and drop produce the
        // same diagram when both apply; the ungated unshift is preferred and
        // the kernel is the authority on its side condition.
        const unshift: ProofStep = {
          rule: 'arityUnshift',
          wire: grab.wire,
          position: grab.position,
        }
        try {
          applyStep(
            diagram,
            unshift,
            this.#options.context(),
            this.#options.orientation(),
          )
        } catch {
          this.#commit('argDrop', {
            rule: 'argDrop',
            wire: grab.wire,
            position: grab.position,
          }, sample)
          return
        }
        this.#commit('arityUnshift', unshift, sample)
        return
      }
      case 'cutRing': {
        const disc = this.#discAt(point)
        if (
          disc === null
          || diagram.nodes[disc.node]?.region !== grab.region
        ) {
          this.#options.refuse(
            'release on the end this cut wraps',
            sample.client,
          )
          return
        }
        this.#commit('cutAbsorb', {
          rule: 'cutAbsorb',
          wire: disc.wire,
        }, sample)
        return
      }
    }
  }

  #arity(diagram: Diagram, wire: WireId): number {
    const sig = diagram.wires[wire]?.sig
    return sig?.kind === 'rel' ? sig.args.length : 0
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
