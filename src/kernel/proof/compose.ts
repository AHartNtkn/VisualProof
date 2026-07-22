import type { Diagram, Endpoint, WireId } from '../diagram/diagram'
import type { DiagramIso } from '../diagram/canonical/explore'
import { exploreIso } from '../diagram/canonical/explore'
import type { SubgraphSelection } from '../diagram/subgraph/selection'
import type { OccurrenceCertificate } from '../diagram/subgraph/occurrence-certificate'
import type { ProofStep } from './step'
import type { ProofContext } from './context'
import { assertProofContext } from './context'
import { applyStepWithReceipt, transportBoundary } from './step'
import { allocationReservation, type ProofAction } from './action'
import { ProofError } from './error'

export type CompositionBoundaries = {
  readonly target: readonly WireId[]
  readonly source: readonly WireId[]
}

export type CompositionOptions = {
  readonly boundaries?: CompositionBoundaries
  readonly orientation?: 'forward' | 'backward'
}

function mapId<T extends string>(m: ReadonlyMap<string, string>, id: T, what: string): T {
  const img = m.get(id)
  if (img === undefined) throw new ProofError(`composition cannot map ${what} '${id}': not present at the meet`)
  return img as T
}

function mapSel(iso: DiagramIso, sel: SubgraphSelection): SubgraphSelection {
  return {
    region: mapId(iso.regions, sel.region, 'region'),
    regions: sel.regions.map((r) => mapId(iso.regions, r, 'region')),
    nodes: sel.nodes.map((n) => mapId(iso.nodes, n, 'node')),
    wires: sel.wires.map((w) => mapId(iso.wires, w, 'wire')),
  }
}

function mapEndpoint(iso: DiagramIso, ep: Endpoint): Endpoint {
  return { node: mapId(iso.nodes, ep.node, 'node'), port: ep.port }
}

function mapOccurrenceCertificate(iso: DiagramIso, certificate: OccurrenceCertificate): OccurrenceCertificate {
  return {
    region: mapId(iso.regions, certificate.region, 'region'),
    regionMap: new Map([...certificate.regionMap].map(([pattern, host]) => [
      pattern, mapId(iso.regions, host, 'region'),
    ])),
    nodeMap: new Map([...certificate.nodeMap].map(([pattern, host]) => [
      pattern, mapId(iso.nodes, host, 'node'),
    ])),
    wireMap: new Map([...certificate.wireMap].map(([pattern, host]) => [
      pattern, mapId(iso.wires, host, 'wire'),
    ])),
    attachments: certificate.attachments.map((wire) => mapId(iso.wires, wire, 'wire')),
    termCertificates: certificate.termCertificates,
  }
}

/**
 * Rewrite one step's HOST ids through an isomorphism. Embedded patterns
 * (DiagramWithBoundary values) are self-contained namespaces and terms are
 * port-name-internal — neither is mapped.
 */
export function mapStepIds(step: ProofStep, iso: DiagramIso): ProofStep {
  switch (step.rule) {
    case 'openTermSpawn':
    case 'relationSpawn':
      return { ...step, region: mapId(iso.regions, step.region, 'region') }
    case 'boundRelationSpawn':
      return { ...step, region: mapId(iso.regions, step.region, 'region'), wire: mapId(iso.wires, step.wire, 'wire') }
    case 'wireJoin':
      return { ...step, a: mapId(iso.wires, step.a, 'wire'), b: mapId(iso.wires, step.b, 'wire') }
    case 'erasure':
      return { ...step, sel: mapSel(iso, step.sel) }
    case 'wireSever':
      return { ...step, wire: mapId(iso.wires, step.wire, 'wire'), keep: step.keep.map((ep) => mapEndpoint(iso, ep)) }
    case 'iteration':
      return { ...step, sel: mapSel(iso, step.sel), target: mapId(iso.regions, step.target, 'region') }
    case 'deiteration':
      return {
        ...step,
        sel: mapSel(iso, step.sel),
        justifier: mapSel(iso, step.justifier),
        certificate: mapOccurrenceCertificate(iso, step.certificate),
      }
    case 'doubleCutIntro':
      return { ...step, sel: mapSel(iso, step.sel) }
    case 'doubleCutElim':
      return { ...step, region: mapId(iso.regions, step.region, 'region') }
    case 'inconsistentCutElim':
      return {
        ...step,
        region: mapId(iso.regions, step.region, 'region'),
        first: mapId(iso.nodes, step.first, 'node'),
        second: mapId(iso.nodes, step.second, 'node'),
      }
    case 'conversion': {
      const attachments = Object.create(null) as Record<string, WireId>
      for (const [name, w] of Object.entries(step.attachments)) attachments[name] = mapId(iso.wires, w, 'wire')
      return { ...step, node: mapId(iso.nodes, step.node, 'node'), attachments }
    }
    case 'congruenceJoin':
      return { ...step, a: mapId(iso.nodes, step.a, 'node'), b: mapId(iso.nodes, step.b, 'node') }
    case 'anchoredWireSplit':
      return {
        ...step,
        wire: mapId(iso.wires, step.wire, 'wire'),
        witness: mapId(iso.nodes, step.witness, 'node'),
        endpoints: step.endpoints.map((endpoint) => mapEndpoint(iso, endpoint)),
        target: mapId(iso.regions, step.target, 'region'),
      }
    case 'anchoredWireContract':
      return {
        ...step,
        redundant: mapId(iso.nodes, step.redundant, 'node'),
        survivor: mapId(iso.nodes, step.survivor, 'node'),
      }
    case 'headStrip':
      return { ...step, a: mapId(iso.nodes, step.a, 'node'), b: mapId(iso.nodes, step.b, 'node') }
    case 'closedTermIntro':
      return { ...step, region: mapId(iso.regions, step.region, 'region') }
    case 'fusion':
      return { ...step, wire: mapId(iso.wires, step.wire, 'wire') }
    case 'fission':
      return { ...step, node: mapId(iso.nodes, step.node, 'node') }
    case 'theorem':
      return { ...step, at: { sel: mapSel(iso, step.at.sel), args: step.at.args.map((w) => mapId(iso.wires, w, 'wire')) } }
    case 'vacuousIntro':
      return {
        ...step,
        scope: mapId(iso.regions, step.scope, 'region'),
        ...(step.body !== undefined
          ? { body: { content: step.body.content, params: step.body.params.map((w) => mapId(iso.wires, w, 'wire')) } }
          : {}),
      }
    case 'vacuousElim':
      return { ...step, wireId: mapId(iso.wires, step.wireId, 'wire') }
    case 'bodyAttach':
      return {
        ...step,
        wireId: mapId(iso.wires, step.wireId, 'wire'),
        params: step.params.map((w) => mapId(iso.wires, w, 'wire')),
      }
    case 'bodyDetach':
      return { ...step, bodyNodeId: mapId(iso.nodes, step.bodyNodeId, 'node') }
    case 'unfold':
      return { ...step, nodeId: mapId(iso.nodes, step.nodeId, 'node') }
    case 'fold':
      return {
        ...step,
        occurrence: mapSel(iso, step.occurrence),
        args: step.args.map((w) => mapId(iso.wires, w, 'wire')),
        target: 'wireId' in step.target
          ? { ...step.target, wireId: mapId(iso.wires, step.target.wireId, 'wire') }
          : step.target,
      }
  }
}

/**
 * Meet-in-the-middle: transplant a tail of actions recorded against
 * `meetSource` onto the isomorphic `meetTarget`. Fresh ids minted during
 * replay depend on the id environment, so a single up-front rewrite cannot
 * work — instead the isomorphism is re-derived from canonical labelings
 * after every step (appliers are iso-equivariant up to fresh-id choice).
 * Optional ordered meet boundaries pin each isomorphism and are transported
 * position-by-position through both actual step receipts. Empty boundaries
 * are the closed-diagram specialization.
 */
export function composeActions(
  meetTarget: Diagram,
  meetSource: Diagram,
  tail: readonly ProofAction[],
  ctx: ProofContext,
  options: CompositionOptions = {},
): ProofAction[] {
  assertProofContext(ctx)
  const boundaries = options.boundaries ?? { target: [], source: [] }
  const orientation = options.orientation ?? 'forward'
  if (boundaries.source.length !== boundaries.target.length) {
    throw new ProofError(
      `the two sides do not meet: boundary arity differs (source ${boundaries.source.length}, target ${boundaries.target.length})`,
    )
  }
  let sourceBoundary = boundaries.source
  let targetBoundary = boundaries.target
  let iso = exploreIso(meetSource, meetTarget, sourceBoundary, targetBoundary)
  if (iso === null) {
    throw new ProofError('the two sides do not meet: the diagrams or ordered boundaries are not isomorphic')
  }
  let curTarget = meetTarget
  let curSource = meetSource
  const out: ProofAction[] = []
  for (const [actionIndex, action] of tail.entries()) {
    const reservation = allocationReservation(action.allocation)
    const mappedSteps: ProofStep[] = []
    for (const [stepIndex, step] of action.steps.entries()) {
      const mapped = mapStepIds(step, iso)
      mappedSteps.push(mapped)
      try {
        const targetReceipt = applyStepWithReceipt(curTarget, mapped, ctx, orientation, reservation)
        const sourceReceipt = applyStepWithReceipt(curSource, step, ctx, orientation, reservation)
        const mappedTargetBoundary = transportBoundary(targetReceipt.interface, targetBoundary)
        const mappedSourceBoundary = transportBoundary(sourceReceipt.interface, sourceBoundary)
        if (mappedTargetBoundary === undefined || mappedSourceBoundary === undefined) {
          const failures: string[] = []
          if (mappedTargetBoundary === undefined) {
            const position = targetBoundary.findIndex((wire) => targetReceipt.interface.image(wire) === undefined)
            failures.push(`target boundary position ${position} has no semantic image`)
          }
          if (mappedSourceBoundary === undefined) {
            const position = sourceBoundary.findIndex((wire) => sourceReceipt.interface.image(wire) === undefined)
            failures.push(`source boundary position ${position} has no semantic image`)
          }
          throw new ProofError(failures.join('; '))
        }
        curTarget = targetReceipt.result
        curSource = sourceReceipt.result
        targetBoundary = mappedTargetBoundary
        sourceBoundary = mappedSourceBoundary
      } catch (e) {
        throw new ProofError(
          `composing action ${actionIndex} step ${stepIndex} (${step.rule}) failed: ${e instanceof Error ? e.message : String(e)}`,
        )
      }
      iso = exploreIso(curSource, curTarget, sourceBoundary, targetBoundary)
      if (iso === null) {
        throw new ProofError(
          `composing action ${actionIndex} step ${stepIndex} (${step.rule}) diverged: the sides are no longer isomorphic`,
        )
      }
    }
    out.push({
      label: action.label,
      steps: mappedSteps,
      placements: action.placements,
      ...(action.allocation === undefined ? {} : { allocation: action.allocation }),
    })
  }
  return out
}
