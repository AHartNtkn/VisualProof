import { checkConversion, type ConversionCertificate } from '../term/certificate'
import { freePorts, type Term } from '../term/term'
import {
  DiagramError,
  mkDiagram,
  portKey,
  type Diagram,
  type Endpoint,
  type NodeId,
  type RegionId,
  type Wire,
  type WireId,
} from '../diagram/diagram'
import { cutDepth, isAncestorOrEqual } from '../diagram/regions'
import { freshId, type IdReservation } from '../diagram/subgraph/freshId'
import { RuleError } from './error'
import { termNodeAt, wireAt } from './access'

function requireClosed(witnessId: NodeId, term: Term): void {
  const free = freePorts(term)
  if (free.length > 0) {
    throw new RuleError(
      `anchored wire rules require a closed witness; '${witnessId}' has free ports [${free.map((name) => `'${name}'`).join(', ')}]`,
    )
  }
}

function sameEndpoint(left: Endpoint, right: Endpoint): boolean {
  return left.node === right.node && portKey(left.port) === portKey(right.port)
}

export function anchorAvailability(d: Diagram, witnessId: NodeId): RegionId {
  const witness = termNodeAt(d, witnessId)
  requireClosed(witnessId, witness.term)
  const wire = wireAt(d, witnessId, { kind: 'output' })
  const scope = d.wires[wire]!.scope
  const depth = cutDepth(d, witness.region)
  let available = witness.region
  while (available !== scope) {
    const region = d.regions[available]!
    if (region.kind === 'sheet') break
    if (cutDepth(d, region.parent) !== depth) break
    available = region.parent
  }
  return available
}

export function applyAnchoredWireSplit(
  d: Diagram,
  wireId: WireId,
  witnessId: NodeId,
  endpoints: readonly Endpoint[],
  target: RegionId,
  reservation?: IdReservation,
): Diagram {
  const witness = termNodeAt(d, witnessId)
  const source = d.wires[wireId]
  if (source === undefined) throw new DiagramError(`unknown wire '${wireId}'`)
  if (wireAt(d, witnessId, { kind: 'output' }) !== wireId) {
    throw new RuleError(`witness '${witnessId}' does not anchor wire '${wireId}'`)
  }
  const available = anchorAvailability(d, witnessId)
  if (!isAncestorOrEqual(d, available, target)) {
    throw new RuleError(`split target '${target}' lies outside witness '${witnessId}' availability '${available}'`)
  }
  const seen = new Set<string>()
  const chosen = (candidate: Endpoint): boolean => endpoints.some((endpoint) => sameEndpoint(endpoint, candidate))
  for (const endpoint of endpoints) {
    const key = `${endpoint.node}/${portKey(endpoint.port)}`
    if (seen.has(key)) throw new RuleError(`split endpoint '${key}' is selected more than once`)
    seen.add(key)
    if (!source.endpoints.some((candidate) => sameEndpoint(candidate, endpoint))) {
      throw new RuleError(`split endpoint '${key}' is not on wire '${wireId}'`)
    }
    if (endpoint.node === witnessId && endpoint.port.kind === 'output') {
      throw new RuleError(`split cannot move witness '${witnessId}'s output`)
    }
    if (!isAncestorOrEqual(d, target, d.nodes[endpoint.node]!.region)) {
      throw new RuleError(`split endpoint '${key}' lies outside target '${target}'`)
    }
  }
  const duplicate = freshId(new Set(Object.keys(d.nodes)), `${witnessId}_split`, reservation?.nodes)
  const freshWire = freshId(new Set(Object.keys(d.wires)), `${wireId}_split`, reservation?.wires)
  return mkDiagram({
    root: d.root,
    regions: { ...d.regions },
    nodes: {
      ...d.nodes,
      [duplicate]: { kind: 'term', region: target, term: witness.term, freePorts: witness.freePorts },
    },
    wires: {
      ...d.wires,
      [wireId]: { scope: source.scope, endpoints: source.endpoints.filter((endpoint) => !chosen(endpoint)) },
      [freshWire]: {
        scope: target,
        endpoints: [{ node: duplicate, port: { kind: 'output' } }, ...endpoints],
      },
    },
  })
}

export function applyAnchoredWireContract(
  d: Diagram,
  redundantId: NodeId,
  survivorId: NodeId,
  certificate: ConversionCertificate,
): Diagram {
  if (redundantId === survivorId) throw new RuleError(`anchored contraction needs two distinct witnesses`)
  const redundant = termNodeAt(d, redundantId)
  const survivor = termNodeAt(d, survivorId)
  requireClosed(redundantId, redundant.term)
  requireClosed(survivorId, survivor.term)
  const checked = checkConversion(redundant.term, survivor.term, certificate)
  if (!checked.ok) throw new RuleError(`anchored contraction certificate rejected: ${checked.reason}`)
  const dropId = wireAt(d, redundantId, { kind: 'output' })
  const keepId = wireAt(d, survivorId, { kind: 'output' })
  if (dropId === keepId) throw new RuleError(`anchored witnesses already share wire '${dropId}'`)
  if (cutDepth(d, d.wires[dropId]!.scope) !== cutDepth(d, redundant.region)) {
    throw new RuleError(`redundant witness '${redundantId}' is shielded from wire '${dropId}'s scope`)
  }
  const available = anchorAvailability(d, survivorId)
  const moved = d.wires[dropId]!.endpoints.filter((endpoint) =>
    !(endpoint.node === redundantId && endpoint.port.kind === 'output'))
  for (const endpoint of moved) {
    if (!isAncestorOrEqual(d, available, d.nodes[endpoint.node]!.region)) {
      throw new RuleError(
        `endpoint '${endpoint.node}/${portKey(endpoint.port)}' lies outside survivor '${survivorId}' availability '${available}'`,
      )
    }
  }
  const nodes = { ...d.nodes }
  delete nodes[redundantId]
  const wires: Record<WireId, Wire> = {}
  for (const [id, wire] of Object.entries(d.wires)) {
    if (id === dropId) continue
    wires[id] = id === keepId
      ? { scope: wire.scope, endpoints: [...wire.endpoints, ...moved] }
      : wire
  }
  return mkDiagram({ root: d.root, regions: { ...d.regions }, nodes, wires })
}
