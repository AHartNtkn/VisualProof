import type { Term } from '../term/term'
import { freePorts, port, renameFreePorts } from '../term/term'
import type { PathSeg } from '../term/reduce'
import { subtermAt, replaceSubtermAt, isBvarClosed, substPort, freshPortName } from '../term/path'
import type { Diagram, DiagramNode, Endpoint, NodeId, Wire, WireId } from '../diagram/diagram'
import { DiagramError, mkDiagram } from '../diagram/diagram'
import { freshId, type IdReservation } from '../diagram/subgraph/freshId'
import { RuleError } from './error'
import { termNodeAt, wireAt } from './access'

/**
 * Rule 6a (spec §3.1), fusion: inline a producer node along its output wire
 * into the single consumer — the one-point rule ∃w (w = t ∧ Φ(w)) ⟺ Φ(t).
 * Requirements: the wire has exactly the producer's output endpoint and one
 * consumer freeVar endpoint (nothing else observes w); the producer sits AT
 * the wire's scope (the equation must be a conjunct at the quantifier's
 * location); producer ≠ consumer (a self-loop is a recursive equation).
 * Equivalence — no polarity gate. Producer ports colliding with the
 * consumer's residual ports are freshened unless both sides already share
 * the same wire.
 */
export function applyFusion(d: Diagram, wireId: WireId): Diagram {
  const w = d.wires[wireId]
  if (w === undefined) throw new DiagramError(`unknown wire '${wireId}'`)
  if (w.endpoints.length !== 2) {
    throw new RuleError(`fusion requires a wire with exactly two endpoints; '${wireId}' has ${w.endpoints.length}`)
  }
  let producerId: NodeId | undefined
  let consumerId: NodeId | undefined
  let consumedPort: string | undefined
  for (const ep of w.endpoints) {
    if (ep.port.kind === 'output') producerId = ep.node
    else if (ep.port.kind === 'freeVar') { consumerId = ep.node; consumedPort = ep.port.name }
  }
  if (producerId === undefined || consumerId === undefined || consumedPort === undefined) {
    throw new RuleError(`fusion requires one output endpoint and one freeVar endpoint on wire '${wireId}'`)
  }
  if (producerId === consumerId) {
    throw new RuleError(`fusion cannot inline a node into itself ('${producerId}'); the equation is recursive`)
  }
  const a = termNodeAt(d, producerId)
  const b = termNodeAt(d, consumerId)
  if (a.region !== w.scope) {
    throw new RuleError(
      `fusion requires the producing node to sit at the wire's scope; node '${producerId}' is in '${a.region}' but wire '${wireId}' is scoped at '${w.scope}'`,
    )
  }

  // Re-express both terms in one private carrier whose names denote global
  // wires. This is the TS counterpart of Lean's fusionTerm: equal wires
  // collapse even when their node-local names differ, while equal local names
  // on different wires remain distinct. Compact only after substitution.
  const taken = new Set<string>([...a.freePorts, ...b.freePorts])
  const carrierByWire = new Map<WireId, string>()
  const wireByCarrier = new Map<string, WireId>()
  let carrierIndex = 0
  const carrierFor = (sourceWire: WireId): string => {
    const existing = carrierByWire.get(sourceWire)
    if (existing !== undefined) return existing
    const carrier = freshPortName(taken, `__fusion_wire_${carrierIndex++}`)
    taken.add(carrier)
    carrierByWire.set(sourceWire, carrier)
    wireByCarrier.set(carrier, sourceWire)
    return carrier
  }
  const producerRenames = new Map(a.freePorts.map((name) => [
    name,
    carrierFor(wireAt(d, producerId, { kind: 'freeVar', name })),
  ]))
  const consumerRenames = new Map(b.freePorts.map((name) => [
    name,
    carrierFor(wireAt(d, consumerId, { kind: 'freeVar', name })),
  ]))
  const producerGlobal = renameFreePorts(a.term, producerRenames)
  const consumerGlobal = renameFreePorts(b.term, consumerRenames)
  const consumedCarrier = consumerRenames.get(consumedPort)!
  const mergedTerm = substPort(consumerGlobal, consumedCarrier, producerGlobal)
  const mergedFreePorts = freePorts(mergedTerm)

  const nodes: Record<NodeId, DiagramNode> = {}
  for (const [id, n] of Object.entries(d.nodes)) {
    if (id === producerId) continue
    nodes[id] = id === consumerId
      ? { kind: 'term', region: b.region, term: mergedTerm, freePorts: mergedFreePorts }
      : n
  }
  const wires: Record<WireId, Wire> = {}
  for (const [id, wv] of Object.entries(d.wires)) {
    if (id === wireId) continue
    const kept = wv.endpoints.filter((ep) =>
      ep.node !== producerId && !(ep.node === consumerId && ep.port.kind === 'freeVar'))
    const adds = mergedFreePorts
      .filter((carrier) => wireByCarrier.get(carrier) === id)
      .map((carrier): Endpoint => ({ node: consumerId!, port: { kind: 'freeVar', name: carrier } }))
    wires[id] = { scope: wv.scope, endpoints: [...kept, ...adds] }
  }
  return mkDiagram({ root: d.root, regions: { ...d.regions }, nodes, wires })
}

/**
 * Rule 6b, fission: extract a bvar-closed subterm to a fresh producer node
 * wired to a fresh port of the residual — fusion's exact inverse. The new
 * node and wire live at the host node's region so applyFusion can undo it.
 */
export function applyFission(d: Diagram, nodeId: NodeId, path: readonly PathSeg[], reservation?: IdReservation): Diagram {
  const node = termNodeAt(d, nodeId)
  // Interpret every local free-port name through its host wire before
  // extraction. Distinct local names on one wire denote one individual and
  // therefore become one support position in each resulting node.
  const taken = new Set(node.freePorts)
  const carrierByWire = new Map<WireId, string>()
  const wireByCarrier = new Map<string, WireId>()
  let carrierIndex = 0
  const carrierFor = (wire: WireId): string => {
    const existing = carrierByWire.get(wire)
    if (existing !== undefined) return existing
    const carrier = freshPortName(taken, `__fission_wire_${carrierIndex++}`)
    taken.add(carrier)
    carrierByWire.set(wire, carrier)
    wireByCarrier.set(carrier, wire)
    return carrier
  }
  const globalRenames = new Map(node.freePorts.map((name) => [
    name,
    carrierFor(wireAt(d, nodeId, { kind: 'freeVar', name })),
  ]))
  const globalTerm = renameFreePorts(node.term, globalRenames)
  let sub: Term
  try {
    sub = subtermAt(globalTerm, path)
  } catch (e) {
    throw new DiagramError(`invalid path into node '${nodeId}': ${e instanceof Error ? e.message : String(e)}`)
  }
  if (!isBvarClosed(sub)) {
    throw new RuleError(`fission requires a bvar-closed subterm; the subterm at [${path.join(', ')}] references binders above it`)
  }
  const q = freshPortName(taken, 'q')
  const residualTerm = replaceSubtermAt(globalTerm, path, port(q))
  const residualFreePorts = freePorts(residualTerm)
  const producerFreePorts = freePorts(sub)
  const producerId = freshId(new Set(Object.keys(d.nodes)), `${nodeId}_fis`, reservation?.nodes)
  const newWireId = freshId(new Set(Object.keys(d.wires)), `${nodeId}_fis`, reservation?.wires)

  const nodes: Record<NodeId, DiagramNode> = {
    ...d.nodes,
    [nodeId]: { kind: 'term', region: node.region, term: residualTerm, freePorts: residualFreePorts },
    [producerId]: { kind: 'term', region: node.region, term: sub, freePorts: producerFreePorts },
  }
  const wires: Record<WireId, Wire> = {}
  for (const [id, w] of Object.entries(d.wires)) {
    const adds: Endpoint[] = residualFreePorts
      .filter((name) => name !== q && wireByCarrier.get(name) === id)
      .map((name): Endpoint => ({ node: nodeId, port: { kind: 'freeVar', name } }))
    for (const name of producerFreePorts) {
      if (wireByCarrier.get(name) === id) {
        adds.push({ node: producerId, port: { kind: 'freeVar', name } })
      }
    }
    const kept = w.endpoints.filter(
      (ep) => !(ep.node === nodeId && ep.port.kind === 'freeVar'),
    )
    wires[id] = { scope: w.scope, endpoints: [...kept, ...adds] }
  }
  wires[newWireId] = {
    scope: node.region,
    endpoints: [
      { node: producerId, port: { kind: 'output' } },
      { node: nodeId, port: { kind: 'freeVar', name: q } },
    ],
  }
  return mkDiagram({ root: d.root, regions: { ...d.regions }, nodes, wires })
}
