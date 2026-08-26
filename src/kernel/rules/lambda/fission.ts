import type {
  Diagram,
  DiagramNode,
  Endpoint,
  NodeId,
  Wire,
  WireId,
} from '../../diagram/diagram'
import { DiagramError, mkDiagram } from '../../diagram/diagram'
import { derivedScope } from '../../diagram/regions'
import { IOTA } from '../../diagram/sig'
import { freshId, type IdReservation } from '../../diagram/subgraph/freshId'
import type { PathSeg } from '../../term/reduce'
import { isBoundClosed, replaceSubtermAt, subtermAt, substFree } from '../../term/path'
import { application, free, lambda, type Term } from '../../term/term'
import { termNodeAt, wireAt } from '../access'
import { RuleError } from '../error'
import { completeWireEnds, type PartsInProgress } from '../wire-ends'

function mapFreeSlots(term: Term, mapping: readonly number[]): Term {
  switch (term.kind) {
    case 'bound': return term
    case 'free': {
      const slot = mapping[term.slot]
      if (slot === undefined) {
        throw new DiagramError(`term free slot ${term.slot} is outside its node interface`)
      }
      return free(slot)
    }
    case 'lambda': return lambda(mapFreeSlots(term.body, mapping))
    case 'application':
      return application(
        mapFreeSlots(term.fn, mapping),
        mapFreeSlots(term.argument, mapping),
      )
  }
}

function usedSlots(term: Term): number[] {
  const result: number[] = []
  const seen = new Set<number>()
  const visit = (current: Term): void => {
    switch (current.kind) {
      case 'bound': return
      case 'free':
        if (!seen.has(current.slot)) {
          seen.add(current.slot)
          result.push(current.slot)
        }
        return
      case 'lambda':
        visit(current.body)
        return
      case 'application':
        visit(current.fn)
        visit(current.argument)
    }
  }
  visit(term)
  return result
}

function compactTerm(
  term: Term,
  carrierWires: readonly WireId[],
): { readonly term: Term; readonly wires: readonly WireId[] } {
  const slots = usedSlots(term)
  const mapping: number[] = []
  const wires: WireId[] = []
  const byWire = new Map<WireId, number>()
  for (const slot of slots) {
    const wire = carrierWires[slot]
    if (wire === undefined) {
      throw new DiagramError(`term carrier slot ${slot} has no host wire`)
    }
    let compact = byWire.get(wire)
    if (compact === undefined) {
      compact = wires.length
      byWire.set(wire, compact)
      wires.push(wire)
    }
    mapping[slot] = compact
  }
  return { term: mapFreeSlots(term, mapping), wires }
}

/** Extract one bound-closed occurrence onto a fresh producer and bridge wire. */
export function applyLambdaFission(
  diagram: Diagram,
  nodeId: NodeId,
  path: readonly PathSeg[],
  reservation?: IdReservation,
): Diagram {
  const node = termNodeAt(diagram, nodeId)
  const nativeWires = Array.from({ length: node.freeArity }, (_, index) =>
    wireAt(diagram, nodeId, { kind: 'free', index }))
  const carrierWires: WireId[] = []
  const carrierByWire = new Map<WireId, number>()
  const nativeToCarrier = nativeWires.map((wire) => {
    const existing = carrierByWire.get(wire)
    if (existing !== undefined) return existing
    const carrier = carrierWires.length
    carrierByWire.set(wire, carrier)
    carrierWires.push(wire)
    return carrier
  })
  const globalTerm = mapFreeSlots(node.term, nativeToCarrier)
  let selected: Term
  try {
    selected = subtermAt(globalTerm, path)
  } catch (error) {
    throw new DiagramError(
      `invalid path into node '${nodeId}': `
      + `${error instanceof Error ? error.message : String(error)}`,
    )
  }
  if (!isBoundClosed(selected)) {
    throw new RuleError(
      `fission requires a bound-closed subterm; the subterm at `
      + `[${path.join(', ')}] references binders above it`,
    )
  }

  const bridgeSlot = carrierWires.length
  const residualTerm = replaceSubtermAt(globalTerm, path, free(bridgeSlot))
  const producer = compactTerm(selected, carrierWires)
  const producerId = freshId(
    new Set(Object.keys(diagram.nodes)),
    `${nodeId}_fis`,
    reservation?.nodes,
  )
  const bridge = freshId(
    new Set(Object.keys(diagram.wires)),
    `${nodeId}_fis`,
    reservation?.wires,
  )
  const oldScopes = new Map(carrierWires.map((wire) => [wire, derivedScope(diagram, wire)]))
  const nodes: Record<NodeId, DiagramNode> = {
    ...diagram.nodes,
    [nodeId]: {
      kind: 'term',
      region: node.region,
      term: residualTerm,
      freeArity: bridgeSlot + 1,
    },
    [producerId]: {
      kind: 'term',
      region: node.region,
      term: producer.term,
      freeArity: producer.wires.length,
    },
  }
  const producerSlotByWire = new Map(
    producer.wires.map((wire, index) => [wire, index]),
  )
  const wires: Record<WireId, Wire> = {}
  for (const [wireId, wire] of Object.entries(diagram.wires)) {
    const carrier = carrierByWire.get(wireId)
    const endpoints: Endpoint[] = []
    let replaced = false
    for (const endpoint of wire.endpoints) {
      if (endpoint.node === nodeId && endpoint.port.kind === 'free') {
        if (!replaced && carrier !== undefined) {
          endpoints.push({ node: nodeId, port: { kind: 'free', index: carrier } })
          const producerSlot = producerSlotByWire.get(wireId)
          if (producerSlot !== undefined) {
            endpoints.push({
              node: producerId,
              port: { kind: 'free', index: producerSlot },
            })
          }
          replaced = true
        }
        continue
      }
      endpoints.push(endpoint)
    }
    wires[wireId] = { sig: wire.sig, endpoints }
  }
  wires[bridge] = {
    sig: IOTA,
    endpoints: [
      { node: producerId, port: { kind: 'output' } },
      { node: nodeId, port: { kind: 'free', index: bridgeSlot } },
    ],
  }
  const parts: PartsInProgress = {
    regions: { ...diagram.regions },
    nodes,
    wires,
  }
  for (const [wire, scope] of oldScopes) {
    completeWireEnds(parts, wire, scope, 'Lambda fission', reservation?.nodes)
  }
  return mkDiagram({ root: diagram.root, ...parts })
}

/** Inline a term producer along its private output/free-slot bridge. */
export function applyLambdaFusion(
  diagram: Diagram,
  wireId: WireId,
  reservation?: IdReservation,
): Diagram {
  const bridge = diagram.wires[wireId]
  if (bridge === undefined) throw new DiagramError(`unknown wire '${wireId}'`)
  if (bridge.endpoints.length !== 2) {
    throw new RuleError(
      `fusion requires a wire with exactly two endpoints; `
      + `'${wireId}' has ${bridge.endpoints.length}`,
    )
  }
  const output = bridge.endpoints.find((endpoint) => endpoint.port.kind === 'output')
  const input = bridge.endpoints.find((endpoint) => endpoint.port.kind === 'free')
  if (output === undefined || input === undefined) {
    throw new RuleError(
      `fusion requires one term output and one term free-slot endpoint on wire '${wireId}'`,
    )
  }
  if (output.node === input.node) {
    throw new RuleError(
      `fusion cannot inline a node into itself ('${output.node}'); the equation is recursive`,
    )
  }
  const producer = termNodeAt(diagram, output.node)
  const consumer = termNodeAt(diagram, input.node)
  const scope = derivedScope(diagram, wireId)
  if (producer.region !== scope) {
    throw new RuleError(
      `fusion requires the producing node to sit at the wire's scope; `
      + `node '${output.node}' is in '${producer.region}' but wire '${wireId}' is scoped at '${scope}'`,
    )
  }

  const carrierWires: WireId[] = []
  const byWire = new Map<WireId, number>()
  const carrierFor = (wire: WireId): number => {
    const existing = byWire.get(wire)
    if (existing !== undefined) return existing
    const carrier = carrierWires.length
    byWire.set(wire, carrier)
    carrierWires.push(wire)
    return carrier
  }
  const consumerWires = Array.from({ length: consumer.freeArity }, (_, index) =>
    wireAt(diagram, input.node, { kind: 'free', index }))
  for (const wire of consumerWires) if (wire !== wireId) carrierFor(wire)
  const producerWires = Array.from({ length: producer.freeArity }, (_, index) =>
    wireAt(diagram, output.node, { kind: 'free', index }))
  for (const wire of producerWires) if (wire !== wireId) carrierFor(wire)
  const consumedCarrier = carrierWires.length
  const consumerMapping = consumerWires.map((wire) =>
    wire === wireId ? consumedCarrier : carrierFor(wire))
  const producerMapping = producerWires.map((wire) => carrierFor(wire))
  const mergedTerm = substFree(
    mapFreeSlots(consumer.term, consumerMapping),
    consumedCarrier,
    mapFreeSlots(producer.term, producerMapping),
  )

  const oldScopes = new Map(carrierWires.map((wire) => [wire, derivedScope(diagram, wire)]))
  const nodes: Record<NodeId, DiagramNode> = {}
  for (const [nodeId, node] of Object.entries(diagram.nodes)) {
    if (nodeId === output.node) continue
    nodes[nodeId] = nodeId === input.node
      ? {
          kind: 'term',
          region: consumer.region,
          term: mergedTerm,
          freeArity: carrierWires.length,
        }
      : node
  }
  const wires: Record<WireId, Wire> = {}
  for (const [candidateId, wire] of Object.entries(diagram.wires)) {
    if (candidateId === wireId) continue
    const carrier = byWire.get(candidateId)
    const endpoints: Endpoint[] = []
    let replaced = false
    for (const endpoint of wire.endpoints) {
      const removed = endpoint.node === output.node
        || (endpoint.node === input.node && endpoint.port.kind === 'free')
      if (!removed) {
        endpoints.push(endpoint)
        continue
      }
      if (!replaced && carrier !== undefined) {
        endpoints.push({
          node: input.node,
          port: { kind: 'free', index: carrier },
        })
        replaced = true
      }
    }
    wires[candidateId] = {
      sig: wire.sig,
      endpoints,
    }
  }
  const parts: PartsInProgress = {
    regions: { ...diagram.regions },
    nodes,
    wires,
  }
  for (const [wire, oldScope] of oldScopes) {
    completeWireEnds(parts, wire, oldScope, 'Lambda fusion', reservation?.nodes)
  }
  return mkDiagram({ root: diagram.root, ...parts })
}
