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

  const residual = new Set(freePorts(b.term))
  residual.delete(consumedPort)
  // Identity rides the wire, never the port name (names are canonical
  // positions after construction, so a shared individual is usually spelled
  // differently on the two nodes). A producer port riding the same wire as a
  // consumer residual port IS that individual: collapse it onto the
  // consumer's existing endpoint under the consumer's name.
  const residualWireName = new Map<WireId, string>()
  for (const r of residual) {
    residualWireName.set(wireAt(d, consumerId, { kind: 'freeVar', name: r }), r)
  }
  const taken = new Set<string>([...freePorts(a.term), ...freePorts(b.term)])
  const renames = new Map<string, string>()
  // endpoints to add to the consumer, on the producer's old wires
  const migrations: { readonly wire: WireId; readonly portName: string }[] = []
  for (const n of freePorts(a.term)) {
    const wa = wireAt(d, producerId, { kind: 'freeVar', name: n })
    const shared = residualWireName.get(wa)
    if (shared !== undefined) {
      if (shared !== n) renames.set(n, shared)
      continue // the consumer's existing endpoint carries the merged port
    }
    if (residual.has(n)) {
      // same NAME as a residual port but a different wire: a distinct
      // individual that must not be conflated — freshen it
      const fresh = freshPortName(taken, n)
      taken.add(fresh)
      renames.set(n, fresh)
      migrations.push({ wire: wa, portName: fresh })
    } else {
      migrations.push({ wire: wa, portName: n })
    }
  }
  // simultaneous: a collapse target may equal another producer port's
  // ORIGINAL name; sequential substitution would cascade into it
  const producerTerm = renameFreePorts(a.term, renames)
  const mergedTerm = substPort(b.term, consumedPort, producerTerm)

  const nodes: Record<NodeId, DiagramNode> = {}
  for (const [id, n] of Object.entries(d.nodes)) {
    if (id === producerId) continue
    nodes[id] = id === consumerId ? { kind: 'term', region: b.region, term: mergedTerm } : n
  }
  const wires: Record<WireId, Wire> = {}
  for (const [id, wv] of Object.entries(d.wires)) {
    if (id === wireId) continue
    const kept = wv.endpoints.filter((ep) => ep.node !== producerId)
    const adds = migrations
      .filter((m) => m.wire === id)
      .map((m): Endpoint => ({ node: consumerId!, port: { kind: 'freeVar', name: m.portName } }))
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
  let sub: Term
  try {
    sub = subtermAt(node.term, path)
  } catch (e) {
    throw new DiagramError(`invalid path into node '${nodeId}': ${e instanceof Error ? e.message : String(e)}`)
  }
  if (!isBvarClosed(sub)) {
    throw new RuleError(`fission requires a bvar-closed subterm; the subterm at [${path.join(', ')}] references binders above it`)
  }
  const q = freshPortName(new Set(freePorts(node.term)), 'q')
  const residualTerm = replaceSubtermAt(node.term, path, port(q))
  const residualPorts = new Set(freePorts(residualTerm))
  const producerId = freshId(new Set(Object.keys(d.nodes)), `${nodeId}_fis`, reservation?.nodes)
  const newWireId = freshId(new Set(Object.keys(d.wires)), `${nodeId}_fis`, reservation?.wires)

  const subPortWires = new Map<string, WireId>()
  for (const n of freePorts(sub)) {
    subPortWires.set(n, wireAt(d, nodeId, { kind: 'freeVar', name: n }))
  }

  const nodes: Record<NodeId, DiagramNode> = {
    ...d.nodes,
    [nodeId]: { kind: 'term', region: node.region, term: residualTerm },
    [producerId]: { kind: 'term', region: node.region, term: sub },
  }
  const wires: Record<WireId, Wire> = {}
  for (const [id, w] of Object.entries(d.wires)) {
    const adds: Endpoint[] = []
    for (const [n, wid] of subPortWires) {
      if (wid === id) adds.push({ node: producerId, port: { kind: 'freeVar', name: n } })
    }
    const kept = w.endpoints.filter(
      (ep) => !(ep.node === nodeId && ep.port.kind === 'freeVar' && !residualPorts.has(ep.port.name)),
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
