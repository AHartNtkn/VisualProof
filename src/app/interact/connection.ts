import { mkDiagramWithBoundary, type DiagramWithBoundary } from '../../kernel/diagram/boundary'
import type {
  Diagram,
  Endpoint,
  NodeId,
  RegionId,
  WireId,
} from '../../kernel/diagram/diagram'
import { relSig } from '../../kernel/diagram/sig'
import { extractSubgraph } from '../../kernel/diagram/subgraph/extract'
import type {
  ContentOccurrence,
  WireJoinInput,
  WireSeverInput,
} from '../../kernel/rules/wire-quantifier'
import { carryOver, mkEngine, pkey, type Engine } from '../../view/engine'
import type { Shape, Theme } from '../../view/paint'
import type { Vec2 } from '../../view/vec'
import { computeLegs, existentialStubs, legPaths } from '../../view/wires'
import { addRelationWire } from '../edit'
import {
  buildSelection,
  pendingWireHitTest,
  type Hit,
  type PendingWireGeometry,
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

export type PreparedOccurrence = {
  readonly occurrence: ContentOccurrence
  readonly content: DiagramWithBoundary
  readonly parameters: readonly WireId[]
}

type ExtentHit = Extract<Hit, { readonly kind: 'node' | 'region' }>

type NodeAnchor = {
  readonly kind: 'node'
  readonly id: NodeId
  readonly offset: Vec2
  readonly direction: Vec2
}

type RegionAnchor = {
  readonly kind: 'region'
  readonly id: RegionId
  readonly radial: Vec2
}

type ContactAnchor = NodeAnchor | RegionAnchor

export type PendingOccurrenceContact = {
  readonly hit: ExtentHit
  readonly anchor: ContactAnchor
}

export type PendingRelationState = {
  readonly diagram: Diagram
  readonly engine: Engine
  readonly wire: WireId
  readonly looseEndBody: string
  readonly contacts: readonly PendingOccurrenceContact[]
  readonly occurrences: readonly ContentOccurrence[]
}

export type RelationSelectionAuthority = {
  readonly selection: () => readonly Hit[]
  readonly setSelection: (hits: readonly Hit[]) => void
}

export type ConnectionDragOptions = {
  readonly active: () => boolean
  readonly engine: () => Engine
  readonly viewScale: () => number
  readonly theme: () => Theme
  /** Present only on proof surfaces; construction keeps the iota gesture only. */
  readonly relationSelection?: RelationSelectionAuthority
  readonly commit: (gesture: ConnectionGesture, pointer: Vec2) => boolean
  readonly refuse: (text: string, pointer: Vec2) => void
}

type PreparedTarget = {
  readonly hit: ExtentHit
  readonly prepared: PreparedOccurrence
}

type WirePreview = {
  readonly kind: 'wire'
  readonly source: ConnectionEnd
  readonly from: Vec2
  at: Vec2
  target: ConnectionEnd | null
  occurrence: PreparedTarget | null
  occurrenceError: string | null
}

type FoundingPreview = {
  readonly kind: 'founding'
  readonly from: Vec2
  at: Vec2
}

type PendingPreview = {
  readonly kind: 'pendingBody' | 'pendingLoose'
  readonly from: Vec2
  at: Vec2
  target: PreparedTarget | null
  targetError: string | null
}

type ConnectionPreview = WirePreview | FoundingPreview | PendingPreview

function sameHit(left: Hit, right: Hit): boolean {
  return left.kind === right.kind && left.id === right.id
}

/**
 * Project the one ordered editor selection into the durable kernel operands.
 * Region/node hits own extent. Wire hits own formal membership and order.
 * Every unselected touching attachment remains an ambient parameter.
 */
export function prepareSelectedOccurrence(
  diagram: Diagram,
  hits: readonly Hit[],
): PreparedOccurrence {
  const extentHits = hits.filter(
    (hit): hit is ExtentHit => hit.kind === 'node' || hit.kind === 'region',
  )
  if (extentHits.length === 0) {
    throw new Error('highlight at least one region or node for the occurrence extent')
  }
  const formalWires = hits
    .filter((hit): hit is Extract<Hit, { readonly kind: 'wire' }> =>
      hit.kind === 'wire')
    .map((hit) => hit.id)
  if (new Set(formalWires).size !== formalWires.length) {
    throw new Error('the ordered occurrence selection repeats a formal wire')
  }

  const sel = buildSelection(diagram, extentHits)
  const extracted = extractSubgraph(diagram, sel)
  const stubByAttachment = new Map<WireId, WireId>()
  extracted.attachments.forEach((attachment, index) => {
    stubByAttachment.set(attachment, extracted.pattern.boundary[index]!)
  })
  const formalBoundary = formalWires.map((wire) => {
    const stub = stubByAttachment.get(wire)
    if (stub === undefined) {
      throw new Error(`selected formal wire '${wire}' does not cross the selected extent`)
    }
    return stub
  })
  const selectedFormals = new Set(formalWires)
  const parameters = extracted.attachments.filter(
    (wire) => !selectedFormals.has(wire),
  )
  const parameterBoundary = parameters.map((wire) => stubByAttachment.get(wire)!)

  return Object.freeze({
    occurrence: Object.freeze({
      sel,
      args: Object.freeze(formalWires),
    }),
    content: mkDiagramWithBoundary(
      extracted.pattern.diagram,
      [...formalBoundary, ...parameterBoundary],
    ),
    parameters: Object.freeze(parameters),
  })
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

function occurrenceTargetShapes(
  engine: Engine,
  target: PreparedTarget,
  stroke: string,
  width: number,
): Shape[] {
  if (target.hit.kind === 'node') {
    const body = engine.bodies.get(target.hit.id)
    return body === undefined
      ? []
      : [{
          kind: 'circle',
          center: body.pos,
          r: body.discR * engine.scale,
          fill: null,
          stroke,
          width,
          insetColor: null,
          glow: null,
        }]
  }
  const region = engine.regions.get(target.hit.id)
  return region === undefined
    ? []
    : [{
        kind: 'circle',
        center: region.center,
        r: region.radius,
        fill: null,
        stroke,
        width,
        insetColor: null,
        glow: null,
      }]
}

function unit(vector: Vec2): Vec2 {
  const length = Math.hypot(vector.x, vector.y)
  return length === 0
    ? { x: 1, y: 0 }
    : { x: vector.x / length, y: vector.y / length }
}

function contactAnchor(engine: Engine, hit: ExtentHit, at: Vec2): ContactAnchor {
  if (hit.kind === 'node') {
    const body = engine.bodies.get(hit.id)
    if (body === undefined) throw new Error(`selected node '${hit.id}' has no live geometry`)
    const offset = { x: at.x - body.pos.x, y: at.y - body.pos.y }
    return Object.freeze({
      kind: 'node',
      id: hit.id,
      offset: Object.freeze(offset),
      direction: Object.freeze(unit(offset)),
    })
  }
  const region = engine.regions.get(hit.id)
  if (region === undefined) throw new Error(`selected region '${hit.id}' has no live geometry`)
  return Object.freeze({
    kind: 'region',
    id: hit.id,
    radial: Object.freeze(unit({
      x: at.x - region.center.x,
      y: at.y - region.center.y,
    })),
  })
}

function contactPoint(engine: Engine, contact: PendingOccurrenceContact): Vec2 {
  const anchor = contact.anchor
  if (anchor.kind === 'node') {
    const body = engine.bodies.get(anchor.id)
    if (body === undefined) throw new Error(`selected node '${anchor.id}' has no live geometry`)
    return {
      x: body.pos.x + anchor.offset.x,
      y: body.pos.y + anchor.offset.y,
    }
  }
  const region = engine.regions.get(anchor.id)
  if (region === undefined) throw new Error(`selected region '${anchor.id}' has no live geometry`)
  return {
    x: region.center.x + anchor.radial.x * region.radius,
    y: region.center.y + anchor.radial.y * region.radius,
  }
}

function contactDirection(contact: PendingOccurrenceContact): Vec2 {
  return contact.anchor.kind === 'node'
    ? contact.anchor.direction
    : contact.anchor.radial
}

function pendingLooseEnd(pending: PendingRelationState): Vec2 {
  const body = pending.engine.bodies.get(pending.looseEndBody)
  if (body === undefined) throw new Error(`pending wire '${pending.wire}' has no loose-end body`)
  return body.pos
}

type ResolvedPendingGeometry = PendingWireGeometry & {
  readonly bodyPoint: Vec2
}

function pendingBodyPoint(
  points: readonly Vec2[],
  contacts: readonly PendingOccurrenceContact[],
): Vec2 {
  if (contacts.length === 1) {
    const point = points[0]!
    const direction = contactDirection(contacts[0]!)
    return {
      x: point.x + direction.x * 22,
      y: point.y + direction.y * 22,
    }
  }
  return {
    x: points.reduce((sum, point) => sum + point.x, 0) / points.length,
    y: points.reduce((sum, point) => sum + point.y, 0) / points.length,
  }
}

function pendingGeometry(
  pending: PendingRelationState,
  engine: Engine,
): ResolvedPendingGeometry {
  const contactPoints = pending.contacts.map((contact) =>
    contactPoint(engine, contact))
  const bodyPoint = pendingBodyPoint(contactPoints, pending.contacts)
  const looseEnd = pendingLooseEnd(pending)
  return {
    wire: pending.wire,
    bodyPaths: [
      ...contactPoints.map((contact) => [contact, bodyPoint]),
      [bodyPoint, looseEnd],
    ],
    looseEnd,
    bodyPoint,
  }
}

function containingRegion(engine: Engine, point: Vec2): RegionId {
  let best: { readonly id: RegionId; readonly radius: number } | null = null
  for (const [id, region] of engine.regions) {
    if (engine.d.regions[id]?.kind === 'sheet') continue
    if (
      Math.hypot(point.x - region.center.x, point.y - region.center.y) <= region.radius
      && (best === null || region.radius < best.radius)
    ) best = { id, radius: region.radius }
  }
  return best?.id ?? engine.d.root
}

/** Shared connection grammar. Proof mode adds selection-consuming relation
 * targets and one pending fresh relation wire; construction mode retains only
 * ordinary wire-to-wire manipulation. */
export class ConnectionDragController {
  readonly #options: ConnectionDragOptions
  #preview: ConnectionPreview | null = null
  #pending: PendingRelationState | null = null
  #claimEpoch = 0

  constructor(options: ConnectionDragOptions) {
    this.#options = options
  }

  get pendingState(): PendingRelationState | null {
    return this.#pending
  }

  get hasPendingInteraction(): boolean {
    return this.#pending !== null || this.#preview !== null
  }

  claim(sample: PointerSample): PointerClaim | null {
    if (
      !this.#options.active()
      || sample.button !== 0
      || sample.shiftKey
      || sample.ctrlKey
    ) return null
    const viewport = { scale: this.#options.viewScale() }

    const pendingClaim = this.#claimPending(sample, viewport.scale)
    if (pendingClaim !== null) return this.#issueClaim(pendingClaim)
    if (this.#pending !== null) return null

    const founding = this.#inspectPreparedTarget(sample)
    if (founding.error !== null) {
      return this.#issueClaim(this.#claimInvalidFounding(founding.error))
    }
    if (founding.target !== null) {
      return this.#issueClaim(this.#claimFounding(sample, founding.target))
    }

    const hit = wireManipulationHitTest(
      this.#options.engine(),
      sample.world,
      viewport,
    )
    if (hit === null) return null
    const preview: WirePreview = {
      kind: 'wire',
      source: wireEnd(hit),
      from: sample.world,
      at: sample.world,
      target: null,
      occurrence: null,
      occurrenceError: null,
    }
    this.#preview = preview
    return this.#issueClaim({
      still: 'selection',
      blocksPassiveRelaxation: true,
      move: (next) => {
        preview.at = next.world
        const occurrence = this.#inspectPreparedTarget(next)
        preview.occurrence = occurrence.target
        preview.occurrenceError = occurrence.error
        if (occurrence.target !== null || occurrence.error !== null) {
          preview.target = null
          return
        }
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
        const occurrence = this.#inspectPreparedTarget(next)
        if (occurrence.error !== null) {
          this.#options.refuse(occurrence.error, next.client)
          return
        }
        if (occurrence.target !== null) {
          const sourceWire = this.#options.engine().d.wires[preview.source.wire]
          if (sourceWire?.sig.kind !== 'rel') {
            this.#options.refuse(
              'only a relation wire can land on selected relation content',
              next.client,
            )
            return
          }
          const prepared = occurrence.target.prepared
          const committed = this.#options.commit({
            kind: 'relationJoin',
            input: {
              kind: 'relation',
              wire: preview.source.wire,
              content: prepared.content,
              parameters: prepared.parameters,
            },
          }, next.client)
          if (committed) this.#options.relationSelection?.setSelection([])
          return
        }
        const target = wireManipulationHitTest(
          this.#options.engine(),
          next.world,
          { scale: this.#options.viewScale() },
        )
        if (target === null) {
          this.#options.refuse(
            'release on a line endpoint, another line, or selected relation content',
            next.client,
          )
          return
        }
        this.#options.commit({
          kind: 'wire',
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
    const pending = this.#pending
    if (pending !== null) {
      const geometry = pendingGeometry(pending, engine)
      for (const path of geometry.bodyPaths) {
        out.push({
          kind: 'polyline',
          pts: path,
          stroke: color,
          width: 2.2,
          glow: null,
        })
      }
      for (const point of [geometry.bodyPoint, geometry.looseEnd]) {
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
        out.push(...wireTargetShapes(engine, preview.target, color, 3.2))
      } else if (preview.occurrence !== null) {
        out.push(...occurrenceTargetShapes(
          engine,
          preview.occurrence,
          color,
          3.2,
        ))
      }
    } else if (preview.kind === 'pendingBody' && preview.target !== null) {
      out.push(...occurrenceTargetShapes(engine, preview.target, color, 3.2))
    }
    return out
  }

  cancel(): void {
    this.#claimEpoch++
    this.#preview = null
    this.#pending = null
  }

  #inspectPreparedTarget(sample: PointerSample): {
    readonly target: PreparedTarget | null
    readonly error: string | null
  } {
    const authority = this.#options.relationSelection
    const hit = sample.hit
    if (
      authority === undefined
      || hit === null
      || (hit.kind !== 'node' && hit.kind !== 'region')
      || !authority.selection().some((candidate) => sameHit(candidate, hit))
    ) return { target: null, error: null }
    try {
      return {
        target: {
          hit,
          prepared: prepareSelectedOccurrence(
            this.#options.engine().d,
            authority.selection(),
          ),
        },
        error: null,
      }
    } catch (error) {
      return {
        target: null,
        error: error instanceof Error ? error.message : String(error),
      }
    }
  }

  #claimFounding(
    sample: PointerSample,
    target: PreparedTarget,
  ): PointerClaim {
    let started = false
    const begin = (at: Vec2): void => {
      if (started) return
      this.#startPending(target, sample.world, at)
      this.#options.relationSelection!.setSelection([])
      this.#preview = {
        kind: 'founding',
        from: sample.world,
        at,
      }
      started = true
    }
    return {
      still: 'selection',
      blocksPassiveRelaxation: true,
      move: (next) => {
        begin(next.world)
        const preview = this.#preview
        if (preview?.kind === 'founding') preview.at = next.world
        this.#setPendingLooseEnd(next.world)
      },
      release: (next, moved) => {
        if (moved) {
          begin(next.world)
          this.#setPendingLooseEnd(next.world)
        }
        this.#preview = null
      },
      cancel: () => {
        this.#preview = null
        if (started) this.#pending = null
      },
    }
  }

  #claimInvalidFounding(message: string): PointerClaim {
    let refused = false
    const refuse = (sample: PointerSample): void => {
      if (refused) return
      refused = true
      this.#options.refuse(message, sample.client)
    }
    return {
      still: 'selection',
      blocksPassiveRelaxation: true,
      move: refuse,
      release: (sample, moved) => {
        if (moved) refuse(sample)
      },
      cancel: () => undefined,
    }
  }

  #claimPending(sample: PointerSample, viewScale: number): PointerClaim | null {
    const pending = this.#pending
    if (pending === null) return null
    const geometry = pendingGeometry(pending, this.#options.engine())
    const hit = pendingWireHitTest(
      geometry,
      sample.world,
      { scale: viewScale },
    )
    if (hit === null) return null
    const kind = hit.kind === 'pendingLooseEnd'
      ? 'pendingLoose' as const
      : 'pendingBody' as const
    const from = kind === 'pendingLoose'
      ? geometry.looseEnd
      : geometry.bodyPoint
    const preview: PendingPreview = {
      kind,
      from,
      at: sample.world,
      target: null,
      targetError: null,
    }
    this.#preview = preview
    return {
      still: 'claim',
      blocksPassiveRelaxation: true,
      move: (next) => {
        preview.at = next.world
        if (kind === 'pendingBody') {
          const inspected = this.#inspectPreparedTarget(next)
          preview.target = inspected.target
          preview.targetError = inspected.error
        }
      },
      release: (next, moved) => {
        this.#preview = null
        if (!moved) return
        if (kind === 'pendingBody') {
          const inspected = this.#inspectPreparedTarget(next)
          if (inspected.error !== null) {
            this.#options.refuse(inspected.error, next.client)
            return
          }
          if (inspected.target === null) {
            this.#options.refuse(
              'release a relation-wire branch on a physically hit selected extent',
              next.client,
            )
            return
          }
          this.#appendPendingContact(
            inspected.target,
            next.world,
          )
          this.#options.relationSelection!.setSelection([])
          return
        }
        this.#finishPending(
          containingRegion(this.#options.engine(), next.world),
          next.world,
          next.client,
        )
      },
      cancel: () => {
        this.#preview = null
      },
    }
  }

  #startPending(
    first: PreparedTarget,
    contactAt: Vec2,
    looseEnd: Vec2,
  ): void {
    const engine = this.#options.engine()
    const sig = relSig(first.prepared.occurrence.args.map(
      (wire) => engine.d.wires[wire]!.sig,
    ))
    const added = addRelationWire(
      engine.d,
      first.prepared.occurrence.sel.region,
      sig,
    )
    const pendingEngine = mkEngine(added.diagram, [])
    carryOver(engine, pendingEngine)
    const looseEndBody = `j:${added.wire}`
    const looseBody = pendingEngine.bodies.get(looseEndBody)
    if (looseBody === undefined) {
      throw new Error(`pending wire '${added.wire}' has no loose-end body`)
    }
    looseBody.pos = { ...looseEnd }
    const contact = Object.freeze({
      hit: first.hit,
      anchor: contactAnchor(engine, first.hit, contactAt),
    })
    this.#pending = Object.freeze({
      diagram: added.diagram,
      engine: pendingEngine,
      wire: added.wire,
      looseEndBody,
      contacts: Object.freeze([contact]),
      occurrences: Object.freeze([first.prepared.occurrence]),
    })
  }

  #appendPendingContact(target: PreparedTarget, at: Vec2): void {
    const pending = this.#pending
    if (pending === null) throw new Error('no pending relation wire to branch')
    const contact = Object.freeze({
      hit: target.hit,
      anchor: contactAnchor(this.#options.engine(), target.hit, at),
    })
    this.#pending = Object.freeze({
      ...pending,
      contacts: Object.freeze([...pending.contacts, contact]),
      occurrences: Object.freeze([
        ...pending.occurrences,
        target.prepared.occurrence,
      ]),
    })
  }

  #setPendingLooseEnd(at: Vec2): void {
    const pending = this.#pending
    if (pending === null) return
    const body = pending.engine.bodies.get(pending.looseEndBody)
    if (body !== undefined) body.pos = { ...at }
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
    const attempt = Object.freeze({
      ...pending,
      diagram: rehomed.diagram,
      engine: pendingEngine,
      wire: rehomed.wire,
      looseEndBody,
    })
    this.#pending = attempt
    const authoritative = attempt.diagram.wires[attempt.wire]!
    const committed = this.#options.commit({
      kind: 'relationSever',
      input: {
        kind: 'relation',
        scope: authoritative.scope,
        occurrences: attempt.occurrences,
      },
    }, pointer)
    this.#pending = committed ? null : pending
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
