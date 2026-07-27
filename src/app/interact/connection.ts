import { mkDiagramWithBoundary, type DiagramWithBoundary } from '../../kernel/diagram/boundary'
import type { Diagram, Endpoint, RegionId, WireId } from '../../kernel/diagram/diagram'
import { relSig } from '../../kernel/diagram/sig'
import { extractSubgraph } from '../../kernel/diagram/subgraph/extract'
import type { ContentOccurrence, WireJoinInput, WireSeverInput } from '../../kernel/rules/wire-quantifier'
import { carryOver, mkEngine, pkey, type Engine } from '../../view/engine'
import type { Shape, Theme } from '../../view/paint'
import type { Vec2 } from '../../view/vec'
import { computeLegs, existentialStubs, legPaths } from '../../view/wires'
import { addRelationWire } from '../edit'
import {
  connectionHitTest,
  membraneCrossingHits,
  pendingWireHitTest,
  type ConnectionHit,
  type MembraneCrossingKey,
  type PendingWireGeometry,
  type PreparedMembrane,
  type WireManipulationHit,
  wireManipulationHitTest,
} from '../hittest'
import type { PointerClaim, PointerSample } from './viewport'

export type ConnectionEnd = {
  readonly wire: WireId
  readonly endpoint: Endpoint | null
}

export type ConnectionGesture =
  | {
      readonly kind: 'wire'
      readonly source: ConnectionEnd
      readonly target: ConnectionEnd
    }
  | {
      readonly kind: 'relationJoin'
      readonly input: Extract<WireJoinInput, { readonly kind: 'relation' }>
    }
  | {
      readonly kind: 'relationSever'
      readonly input: Extract<WireSeverInput, { readonly kind: 'relation' }>
    }

export type PreparedMembraneContent = {
  readonly occurrence: ContentOccurrence
  readonly content: DiagramWithBoundary
  readonly parameters: readonly WireId[]
}

export type PendingMembraneContact = {
  readonly membrane: PreparedMembrane
  readonly at: Vec2
}

export type PendingRelationState = {
  readonly diagram: Diagram
  readonly engine: Engine
  readonly wire: WireId
  readonly looseEndBody: string
  readonly contacts: readonly PendingMembraneContact[]
  readonly occurrences: readonly ContentOccurrence[]
  readonly looseEnd: Vec2
  readonly bodyPoint: Vec2
}

export type ConnectionDragOptions = {
  readonly active: () => boolean
  readonly engine: () => Engine
  readonly viewScale: () => number
  readonly theme: () => Theme
  readonly relationGestures?: boolean
  readonly commit: (gesture: ConnectionGesture, pointer: Vec2) => boolean
  readonly refuse: (text: string, pointer: Vec2) => void
}

type WirePreview = {
  readonly kind: 'wire'
  readonly source: ConnectionEnd
  readonly from: Vec2
  at: Vec2
  target: ConnectionEnd | null
  membrane: PreparedMembrane | null
}

type MembranePreview = {
  readonly kind: 'membrane'
  readonly source: PreparedMembrane
  readonly from: Vec2
  at: Vec2
  target: PreparedMembrane | null
}

type PendingPreview = {
  readonly kind: 'pendingBody' | 'pendingLoose'
  readonly from: Vec2
  at: Vec2
  target: ConnectionHit | null
}

type ConnectionPreview = WirePreview | MembranePreview | PendingPreview

function wireEnd(hit: WireManipulationHit): ConnectionEnd {
  return {
    wire: hit.wire,
    endpoint: hit.kind === 'endpoint' ? hit.endpoint : null,
  }
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

function membraneShape(
  engine: Engine,
  membrane: PreparedMembrane,
  stroke: string,
  width: number,
  fill: string | null = null,
): Shape[] {
  const circle = engine.regions.get(membrane.outer)
  return circle === undefined
    ? []
    : [{
        kind: 'circle',
        center: circle.center,
        r: circle.radius,
        fill,
        stroke,
        width,
        insetColor: null,
        glow: null,
      }]
}

function membraneCenter(engine: Engine, membrane: PreparedMembrane): Vec2 {
  return engine.regions.get(membrane.outer)?.center ?? { x: 0, y: 0 }
}

function pendingGeometry(pending: PendingRelationState): PendingWireGeometry {
  return {
    wire: pending.wire,
    bodyPaths: [
      ...pending.contacts.map((contact) => [contact.at, pending.bodyPoint]),
      [pending.bodyPoint, pending.looseEnd],
    ],
    looseEnd: pending.looseEnd,
  }
}

function pendingBodyPoint(
  engine: Engine,
  contacts: readonly PendingMembraneContact[],
): Vec2 {
  if (contacts.length === 1) {
    const contact = contacts[0]!
    const center = membraneCenter(engine, contact.membrane)
    const dx = contact.at.x - center.x
    const dy = contact.at.y - center.y
    const length = Math.hypot(dx, dy)
    const ux = length === 0 ? 1 : dx / length
    const uy = length === 0 ? 0 : dy / length
    return { x: contact.at.x + ux * 22, y: contact.at.y + uy * 22 }
  }
  return {
    x: contacts.reduce((sum, contact) => sum + contact.at.x, 0) / contacts.length,
    y: contacts.reduce((sum, contact) => sum + contact.at.y, 0) / contacts.length,
  }
}

/**
 * Convert the exact contents of a prepared membrane to the kernel's bounded
 * representation. Crossing taps form the formal prefix in event order; every
 * untapped crossing remains in the extracted canonical order as an ambient
 * parameter suffix.
 */
export function prepareMembraneContent(
  diagram: Diagram,
  membrane: PreparedMembrane,
  taps: readonly MembraneCrossingKey[],
): PreparedMembraneContent {
  const extracted = extractSubgraph(diagram, membrane.selection)
  const stubByAttachment = new Map<WireId, WireId>()
  extracted.attachments.forEach((attachment, index) => {
    stubByAttachment.set(attachment, extracted.pattern.boundary[index]!)
  })
  const formalBoundary = taps.map((tap, index) => {
    if (tap.membrane !== membrane.outer) {
      throw new Error(
        `formal crossing ${index} belongs to membrane '${tap.membrane}', `
        + `not '${membrane.outer}'`,
      )
    }
    const stub = stubByAttachment.get(tap.wire)
    if (stub === undefined) {
      throw new Error(
        `formal crossing ${index} wire '${tap.wire}' does not touch `
        + `membrane '${membrane.outer}'`,
      )
    }
    return stub
  })
  const tapped = new Set(taps.map((tap) => tap.wire))
  const parameters = extracted.attachments.filter((wire) => !tapped.has(wire))
  const parameterBoundary = parameters.map((wire) => stubByAttachment.get(wire)!)
  return Object.freeze({
    occurrence: Object.freeze({
      sel: membrane.selection,
      args: Object.freeze(taps.map((tap) => tap.wire)),
    }),
    content: mkDiagramWithBoundary(
      extracted.pattern.diagram,
      [...formalBoundary, ...parameterBoundary],
    ),
    parameters: Object.freeze(parameters),
  })
}

/**
 * One physical connection grammar for edit and proof modes. Proof mode enables
 * prepared-membrane crossings and pending relation wires; construction mode
 * consumes only the unchanged wire-to-wire branch.
 */
export class ConnectionDragController {
  readonly #options: ConnectionDragOptions
  readonly #taps = new Map<RegionId, MembraneCrossingKey[]>()
  #preview: ConnectionPreview | null = null
  #pending: PendingRelationState | null = null

  constructor(options: ConnectionDragOptions) { this.#options = options }

  get pendingState(): PendingRelationState | null { return this.#pending }
  get hasPendingInteraction(): boolean {
    return this.#pending !== null || this.#preview !== null || this.#taps.size > 0
  }

  claim(sample: PointerSample): PointerClaim | null {
    if (!this.#options.active() || sample.button !== 0 || sample.shiftKey || sample.ctrlKey) return null
    const engine = this.#options.engine()
    const viewport = { scale: this.#options.viewScale() }

    if (this.#options.relationGestures === true) {
      const pendingClaim = this.#claimPending(sample, viewport.scale)
      if (pendingClaim !== null) return pendingClaim
      const relationHit = connectionHitTest(engine, sample.world, viewport)
      if (relationHit?.kind === 'crossing') return this.#claimCrossing(relationHit.key)
      if (this.#pending !== null) return null
      if (relationHit?.kind === 'membrane') {
        return this.#claimMembrane(sample, relationHit.membrane)
      }
    }

    const hit = wireManipulationHitTest(engine, sample.world, viewport)
    if (hit === null) return null
    const preview: WirePreview = {
      kind: 'wire',
      source: wireEnd(hit),
      from: sample.world,
      at: sample.world,
      target: null,
      membrane: null,
    }
    this.#preview = preview
    return {
      still: 'selection',
      blocksPassiveRelaxation: true,
      move: (next) => {
        preview.at = next.world
        if (this.#options.relationGestures === true) {
          const target = connectionHitTest(
            this.#options.engine(),
            next.world,
            { scale: this.#options.viewScale() },
          )
          if (target?.kind === 'membrane') {
            preview.target = null
            preview.membrane = target.membrane
            return
          }
        }
        preview.membrane = null
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
        if (preview.membrane !== null) {
          const sourceWire = this.#options.engine().d.wires[preview.source.wire]
          if (sourceWire?.sig.kind !== 'rel') {
            this.#options.refuse('only a relation wire can land on prepared content', next.client)
            return
          }
          const prepared = this.#prepare(preview.membrane)
          const committed = this.#options.commit({
            kind: 'relationJoin',
            input: {
              kind: 'relation',
              wire: preview.source.wire,
              content: prepared.content,
              parameters: prepared.parameters,
            },
          }, next.client)
          if (committed) this.#clearTaps()
          return
        }
        if (preview.target === null) {
          this.#options.refuse('release on a line endpoint, another line, or prepared membrane', next.client)
          return
        }
        this.#options.commit({
          kind: 'wire',
          source: preview.source,
          target: preview.target,
        }, next.client)
      },
      cancel: () => { this.#preview = null },
    }
  }

  overlay(): readonly Shape[] {
    const engine = this.#options.engine()
    const color = this.#options.theme().interaction.valid
    const out: Shape[] = []
    for (const keys of this.#taps.values()) {
      for (const key of keys) {
        const crossing = membraneCrossingHits(engine).find((hit) =>
          hit.key.membrane === key.membrane && hit.key.wire === key.wire)
        if (crossing === undefined) continue
        out.push({
          kind: 'circle',
          center: crossing.at,
          r: 4 / this.#options.viewScale(),
          fill: color,
          stroke: color,
          width: 1.4,
          insetColor: null,
          glow: null,
        })
      }
    }
    const pending = this.#pending
    if (pending !== null) {
      for (const path of pendingGeometry(pending).bodyPaths) {
        out.push({
          kind: 'polyline',
          pts: path,
          stroke: color,
          width: 2.2,
          glow: null,
        })
      }
      for (const point of [pending.bodyPoint, pending.looseEnd]) {
        out.push({
          kind: 'circle',
          center: point,
          r: 4.5 / this.#options.viewScale(),
          fill: color,
          stroke: color,
          width: 1.2,
          insetColor: null,
          glow: null,
        })
      }
    }
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
    if (preview.kind === 'wire') {
      if (preview.target !== null) {
        out.push(...targetShapes(engine, preview.target, color, 3.2))
      } else if (preview.membrane !== null) {
        out.push(...membraneShape(engine, preview.membrane, color, 3.2))
      }
    } else if (preview.kind === 'membrane' && preview.target !== null) {
      out.push(...membraneShape(engine, preview.target, color, 3.2))
    } else if (preview.kind !== 'membrane' && preview.target?.kind === 'membrane') {
      out.push(...membraneShape(engine, preview.target.membrane, color, 3.2))
    }
    return out
  }

  cancel(): void {
    this.#preview = null
    this.#pending = null
    this.#clearTaps()
  }

  #claimCrossing(key: MembraneCrossingKey): PointerClaim {
    return {
      still: 'claim',
      blocksPassiveRelaxation: true,
      move: () => undefined,
      release: (sample, moved) => {
        if (moved) return
        if (this.#pending?.contacts.some(
          (contact) => contact.membrane.outer === key.membrane,
        ) === true) {
          this.#options.refuse('tap formal crossings before the membrane contact', sample.client)
          return
        }
        const taps = this.#taps.get(key.membrane) ?? []
        this.#taps.set(key.membrane, [...taps, key])
      },
      cancel: () => undefined,
    }
  }

  #claimMembrane(sample: PointerSample, source: PreparedMembrane): PointerClaim {
    this.#startPending(source, sample.world)
    const preview: MembranePreview = {
      kind: 'membrane',
      source,
      from: sample.world,
      at: sample.world,
      target: null,
    }
    this.#preview = preview
    return {
      still: 'claim',
      blocksPassiveRelaxation: true,
      move: (next) => {
        preview.at = next.world
        const target = connectionHitTest(
          this.#options.engine(),
          next.world,
          { scale: this.#options.viewScale() },
        )
        preview.target = target?.kind === 'membrane' ? target.membrane : null
      },
      release: (next, moved) => {
        this.#preview = null
        const target = connectionHitTest(
          this.#options.engine(),
          next.world,
          { scale: this.#options.viewScale() },
        )
        if (!moved) return
        if (target?.kind === 'membrane') {
          this.#appendPendingContact(target.membrane, target.at)
          return
        }
        this.#options.refuse(
          'release a relation endpoint on a prepared membrane; use its loose end for scope',
          next.client,
        )
      },
      cancel: () => {
        this.#preview = null
        this.#pending = null
      },
    }
  }

  #claimPending(sample: PointerSample, viewScale: number): PointerClaim | null {
    const pending = this.#pending
    if (pending === null) return null
    const hit = pendingWireHitTest(
      pendingGeometry(pending),
      sample.world,
      { scale: viewScale },
    )
    if (hit === null) return null
    const kind = hit.kind === 'pendingLooseEnd'
      ? 'pendingLoose' as const
      : 'pendingBody' as const
    const from = kind === 'pendingLoose' ? pending.looseEnd : pending.bodyPoint
    const preview: PendingPreview = {
      kind,
      from,
      at: sample.world,
      target: null,
    }
    this.#preview = preview
    return {
      still: 'claim',
      blocksPassiveRelaxation: true,
      move: (next) => {
        preview.at = next.world
        preview.target = connectionHitTest(
          this.#options.engine(),
          next.world,
          { scale: this.#options.viewScale() },
        )
      },
      release: (next, moved) => {
        this.#preview = null
        if (!moved) return
        const target = connectionHitTest(
          this.#options.engine(),
          next.world,
          { scale: this.#options.viewScale() },
        )
        if (kind === 'pendingBody') {
          if (target?.kind !== 'membrane') {
            this.#options.refuse('release a relation-wire branch on a prepared membrane', next.client)
            return
          }
          this.#appendPendingContact(target.membrane, target.at)
          return
        }
        const scope = this.#scopeOf(target)
        if (scope === null) {
          this.#options.refuse('release the loose relation end into a region', next.client)
          return
        }
        this.#finishPending(scope, next.world, next.client)
      },
      cancel: () => { this.#preview = null },
    }
  }

  #startPending(first: PreparedMembrane, at: Vec2): void {
    const engine = this.#options.engine()
    const firstPrepared = this.#prepare(first)
    const parent = engine.d.regions[first.outer]
    if (parent === undefined || parent.kind === 'sheet') {
      throw new Error(`prepared membrane '${first.outer}' has no enclosing scope`)
    }
    const sig = relSig(firstPrepared.occurrence.args.map((wire) => engine.d.wires[wire]!.sig))
    const added = addRelationWire(engine.d, parent.parent, sig)
    const pendingEngine = mkEngine(added.diagram, [])
    carryOver(engine, pendingEngine)
    const contact = Object.freeze({ membrane: first, at: Object.freeze({ ...at }) })
    const contacts = Object.freeze([contact])
    const bodyPoint = pendingBodyPoint(engine, contacts)
    const looseEndBody = `j:${added.wire}`
    const looseBody = pendingEngine.bodies.get(looseEndBody)
    if (looseBody === undefined) {
      throw new Error(`pending wire '${added.wire}' has no loose-end body`)
    }
    looseBody.pos = {
      x: bodyPoint.x,
      y: bodyPoint.y + 36 / this.#options.viewScale(),
    }
    this.#pending = Object.freeze({
      diagram: added.diagram,
      engine: pendingEngine,
      wire: added.wire,
      looseEndBody,
      contacts,
      occurrences: Object.freeze([firstPrepared.occurrence]),
      bodyPoint: Object.freeze(bodyPoint),
      looseEnd: looseBody.pos,
    })
  }

  #appendPendingContact(membrane: PreparedMembrane, at: Vec2): void {
    const pending = this.#pending
    if (pending === null) throw new Error('no pending relation wire to branch')
    const contact = Object.freeze({
      membrane,
      at: Object.freeze({ ...at }),
    })
    const contacts = Object.freeze([...pending.contacts, contact])
    this.#pending = Object.freeze({
      ...pending,
      contacts,
      occurrences: Object.freeze([
        ...pending.occurrences,
        this.#prepare(membrane).occurrence,
      ]),
      bodyPoint: Object.freeze(pendingBodyPoint(this.#options.engine(), contacts)),
    })
  }

  #prepare(membrane: PreparedMembrane): PreparedMembraneContent {
    return prepareMembraneContent(
      this.#options.engine().d,
      membrane,
      this.#taps.get(membrane.outer) ?? [],
    )
  }

  #scopeOf(hit: ConnectionHit | null): RegionId | null {
    if (hit === null) return null
    if (hit.kind === 'region') return hit.region
    if (hit.kind === 'membrane') return hit.membrane.outer
    return null
  }

  #finishPending(scope: RegionId, looseEnd: Vec2, pointer: Vec2): void {
    const pending = this.#pending
    if (pending === null) throw new Error('no pending relation wire to finish')
    const relation = pending.diagram.wires[pending.wire]
    if (relation?.sig.kind !== 'rel') {
      throw new Error(`pending wire '${pending.wire}' is not relational`)
    }
    const rehomed = addRelationWire(this.#options.engine().d, scope, relation.sig)
    const pendingEngine = mkEngine(rehomed.diagram, [])
    carryOver(pending.engine, pendingEngine)
    const looseEndBody = `j:${rehomed.wire}`
    const looseBody = pendingEngine.bodies.get(looseEndBody)
    if (looseBody === undefined) {
      throw new Error(`pending wire '${rehomed.wire}' has no loose-end body`)
    }
    looseBody.pos = { ...looseEnd }
    this.#pending = Object.freeze({
      ...pending,
      diagram: rehomed.diagram,
      engine: pendingEngine,
      wire: rehomed.wire,
      looseEndBody,
      looseEnd: looseBody.pos,
    })
    const authoritative = this.#pending.diagram.wires[this.#pending.wire]!
    const committed = this.#options.commit({
      kind: 'relationSever',
      input: {
        kind: 'relation',
        scope: authoritative.scope,
        occurrences: this.#pending.occurrences,
      },
    }, pointer)
    this.#pending = null
    if (committed) this.#clearTaps()
  }

  #clearTaps(): void { this.#taps.clear() }
}
