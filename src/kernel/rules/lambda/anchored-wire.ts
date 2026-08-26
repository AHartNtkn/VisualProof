import { checkConversion, type ConversionCertificate } from '../../term/certificate'
import { freeArity } from '../../term/term'
import type {
  Diagram,
  DiagramNode,
  Endpoint,
  NodeId,
  RegionId,
  Wire,
  WireId,
} from '../../diagram/diagram'
import { DiagramError, mkDiagram, portKey } from '../../diagram/diagram'
import {
  cutDepth,
  derivedScope,
  isAncestorOrEqual,
  wireVisibleAt,
} from '../../diagram/regions'
import { freshId, type IdReservation } from '../../diagram/subgraph/freshId'
import { termNodeAt, wireAt } from '../access'
import { RuleError } from '../error'
import { completeWireEnds, type PartsInProgress } from '../wire-ends'

function requireClosed(
  diagram: Diagram,
  witnessId: NodeId,
): Extract<DiagramNode, { readonly kind: 'term' }> {
  const witness = termNodeAt(diagram, witnessId)
  if (freeArity(witness.term) !== 0) {
    throw new RuleError(
      `anchored wire rules require a closed witness; '${witnessId}' uses free slots`,
    )
  }
  return witness
}

function sameEndpoint(left: Endpoint, right: Endpoint): boolean {
  return left.node === right.node && portKey(left.port) === portKey(right.port)
}

/** Highest same-polarity region in which a closed output witness is usable. */
export function anchorAvailability(
  diagram: Diagram,
  witnessId: NodeId,
): RegionId {
  const witness = requireClosed(diagram, witnessId)
  const output = wireAt(diagram, witnessId, { kind: 'output' })
  const scope = derivedScope(diagram, output)
  const depth = cutDepth(diagram, witness.region)
  let available = witness.region
  while (available !== scope) {
    const region = diagram.regions[available]!
    if (region.kind === 'sheet') break
    if (cutDepth(diagram, region.parent) !== depth) break
    available = region.parent
  }
  return available
}

/** Move selected incidences onto a fresh wire anchored by a duplicate witness. */
export function applyLambdaAnchoredWireSplit(
  diagram: Diagram,
  wireId: WireId,
  witnessId: NodeId,
  endpoints: readonly Endpoint[],
  target: RegionId,
  reservation?: IdReservation,
): Diagram {
  const witness = requireClosed(diagram, witnessId)
  const source = diagram.wires[wireId]
  if (source === undefined) throw new DiagramError(`unknown wire '${wireId}'`)
  if (wireAt(diagram, witnessId, { kind: 'output' }) !== wireId) {
    throw new RuleError(`witness '${witnessId}' does not anchor wire '${wireId}'`)
  }
  if (endpoints.length === 0) {
    throw new RuleError('anchored wire split must move at least one endpoint')
  }
  const available = anchorAvailability(diagram, witnessId)
  if (!isAncestorOrEqual(diagram, available, target)) {
    throw new RuleError(
      `split target '${target}' lies outside witness '${witnessId}' availability '${available}'`,
    )
  }
  const seen = new Set<string>()
  for (const endpoint of endpoints) {
    const key = `${endpoint.node}/${portKey(endpoint.port)}`
    if (seen.has(key)) {
      throw new RuleError(`split endpoint '${key}' is selected more than once`)
    }
    seen.add(key)
    if (!source.endpoints.some((candidate) => sameEndpoint(candidate, endpoint))) {
      throw new RuleError(`split endpoint '${key}' is not on wire '${wireId}'`)
    }
    if (endpoint.node === witnessId) {
      throw new RuleError(`split cannot move an incidence of witness '${witnessId}'`)
    }
    const node = diagram.nodes[endpoint.node]
    if (node === undefined) throw new DiagramError(`unknown node '${endpoint.node}'`)
    if (!isAncestorOrEqual(diagram, target, node.region)) {
      throw new RuleError(`split endpoint '${key}' lies outside target '${target}'`)
    }
  }
  for (let slot = 0; slot < witness.freeArity; slot++) {
    const freeWire = wireAt(diagram, witnessId, { kind: 'free', index: slot })
    if (!wireVisibleAt(diagram, freeWire, target)) {
      throw new RuleError(
        `witness free-slot wire '${freeWire}' is not visible at split target '${target}'`,
      )
    }
  }

  const duplicate = freshId(
    new Set(Object.keys(diagram.nodes)),
    `${witnessId}_split`,
    reservation?.nodes,
  )
  const freshWire = freshId(
    new Set(Object.keys(diagram.wires)),
    `${wireId}_split`,
    reservation?.wires,
  )
  const nodes: Record<NodeId, DiagramNode> = {
    ...diagram.nodes,
    [duplicate]: {
      kind: 'term',
      region: target,
      term: witness.term,
      freeArity: witness.freeArity,
    },
  }
  const chosen = (candidate: Endpoint): boolean =>
    endpoints.some((endpoint) => sameEndpoint(endpoint, candidate))
  const wires: Record<WireId, Wire> = {}
  for (const [candidateId, wire] of Object.entries(diagram.wires)) {
    const added: Endpoint[] = []
    for (let slot = 0; slot < witness.freeArity; slot++) {
      if (wireAt(diagram, witnessId, { kind: 'free', index: slot }) === candidateId) {
        added.push({ node: duplicate, port: { kind: 'free', index: slot } })
      }
    }
    wires[candidateId] = {
      sig: wire.sig,
      endpoints: [
        ...wire.endpoints.filter((endpoint) =>
          candidateId !== wireId || !chosen(endpoint)),
        ...added,
      ],
    }
  }
  wires[freshWire] = {
    sig: source.sig,
    endpoints: [
      { node: duplicate, port: { kind: 'output' } },
      ...endpoints,
    ],
  }
  const parts: PartsInProgress = {
    regions: { ...diagram.regions }, nodes, wires,
  }
  completeWireEnds(
    parts,
    wireId,
    derivedScope(diagram, wireId),
    'Lambda anchored wire split',
    reservation?.nodes,
  )
  completeWireEnds(
    parts,
    freshWire,
    target,
    'Lambda anchored wire split',
    reservation?.nodes,
  )
  return mkDiagram({ root: diagram.root, ...parts })
}

/** Merge a redundant closed witness and its output wire into a survivor. */
export function applyLambdaAnchoredWireContract(
  diagram: Diagram,
  redundantId: NodeId,
  survivorId: NodeId,
  certificate: ConversionCertificate,
  reservation?: IdReservation,
): Diagram {
  if (redundantId === survivorId) {
    throw new RuleError('anchored contraction needs two distinct witnesses')
  }
  const redundant = requireClosed(diagram, redundantId)
  const survivor = requireClosed(diagram, survivorId)
  const checked = checkConversion(redundant.term, survivor.term, certificate)
  if (!checked.ok) {
    throw new RuleError(`anchored contraction certificate rejected: ${checked.reason}`)
  }
  const drop = wireAt(diagram, redundantId, { kind: 'output' })
  const keep = wireAt(diagram, survivorId, { kind: 'output' })
  if (drop === keep) {
    throw new RuleError(`anchored witnesses already share wire '${drop}'`)
  }
  const dropScope = derivedScope(diagram, drop)
  if (cutDepth(diagram, dropScope) !== cutDepth(diagram, redundant.region)) {
    throw new RuleError(
      `redundant witness '${redundantId}' is shielded from wire '${drop}'s scope`,
    )
  }
  const available = anchorAvailability(diagram, survivorId)
  const moved = diagram.wires[drop]!.endpoints.filter((endpoint) =>
    endpoint.node !== redundantId)
  for (const endpoint of moved) {
    const node = diagram.nodes[endpoint.node]
    if (node === undefined) throw new DiagramError(`unknown node '${endpoint.node}'`)
    if (!isAncestorOrEqual(diagram, available, node.region)) {
      throw new RuleError(
        `endpoint '${endpoint.node}/${portKey(endpoint.port)}' lies outside `
        + `survivor '${survivorId}' availability '${available}'`,
      )
    }
  }

  const touched = new Set<WireId>()
  for (const [wireId, wire] of Object.entries(diagram.wires)) {
    if (wireId === drop) continue
    if (wire.endpoints.some((endpoint) => endpoint.node === redundantId)) {
      touched.add(wireId)
    }
  }
  const oldScopes = new Map([...touched].map((wire) => [wire, derivedScope(diagram, wire)]))
  const nodes: Record<NodeId, DiagramNode> = { ...diagram.nodes }
  delete nodes[redundantId]
  const wires: Record<WireId, Wire> = {}
  for (const [wireId, wire] of Object.entries(diagram.wires)) {
    if (wireId === drop) continue
    const endpoints = wire.endpoints.filter((endpoint) => endpoint.node !== redundantId)
    wires[wireId] = wireId === keep
      ? { sig: wire.sig, endpoints: [...endpoints, ...moved] }
      : { sig: wire.sig, endpoints }
  }
  const parts: PartsInProgress = {
    regions: { ...diagram.regions }, nodes, wires,
  }
  for (const [wire, scope] of oldScopes) {
    completeWireEnds(parts, wire, scope, 'Lambda anchored wire contract', reservation?.nodes)
  }
  return mkDiagram({ root: diagram.root, ...parts })
}
