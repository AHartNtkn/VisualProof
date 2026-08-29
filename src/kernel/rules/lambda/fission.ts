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
import { free, type Term } from '../../term/term'
import { mapFreeSlots } from '../../term/interface'
import { termNodeAt, wireAt } from '../access'
import { RuleError } from '../error'
import { completeWireEnds, type PartsInProgress } from '../wire-ends'

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
  let selected: Term
  try {
    selected = subtermAt(node.term, path)
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

  const bridgeSlot = node.freeArity
  const residualTerm = replaceSubtermAt(node.term, path, free(bridgeSlot))
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
  const oldScopes = new Map(nativeWires.map((wire) => [wire, derivedScope(diagram, wire)]))
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
      term: selected,
      freeArity: node.freeArity,
    },
  }
  const wires: Record<WireId, Wire> = {}
  for (const [wireId, wire] of Object.entries(diagram.wires)) {
    const endpoints: Endpoint[] = []
    for (const endpoint of wire.endpoints) {
      if (endpoint.node === nodeId && endpoint.port.kind === 'free') {
        endpoints.push(endpoint)
        endpoints.push({
          node: producerId,
          port: { kind: 'free', index: endpoint.port.index },
        })
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
  if (input.port.kind !== 'free') {
    throw new RuleError(`fusion input on wire '${wireId}' is not a term free slot`)
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

  const consumerWires = Array.from({ length: consumer.freeArity }, (_, index) =>
    wireAt(diagram, input.node, { kind: 'free', index }))
  const producerWires = Array.from({ length: producer.freeArity }, (_, index) =>
    wireAt(diagram, output.node, { kind: 'free', index }))
  const carrierWires: WireId[] = []
  const consumerMapping = consumerWires.map((wire) => {
    if (wire === wireId) return -1
    const carrier = carrierWires.length
    carrierWires.push(wire)
    return carrier
  })
  const consumedCarrier = carrierWires.length
  consumerMapping[input.port.index] = consumedCarrier
  const producerMapping = producerWires.map((wire, slot) => {
    const sameNative = consumerMapping[slot]
    if (
      sameNative !== undefined
      && sameNative !== consumedCarrier
      && carrierWires[sameNative] === wire
    ) return sameNative
    const shared = carrierWires.indexOf(wire)
    if (shared >= 0) return shared
    const carrier = carrierWires.length
    carrierWires.push(wire)
    return carrier
  })
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
  const slotsByWire = new Map<WireId, number[]>()
  carrierWires.forEach((wire, slot) => {
    const slots = slotsByWire.get(wire) ?? []
    slots.push(slot)
    slotsByWire.set(wire, slots)
  })
  for (const [candidateId, wire] of Object.entries(diagram.wires)) {
    if (candidateId === wireId) continue
    const endpoints: Endpoint[] = []
    const inserted = new Set<number>()
    const insertSlot = (slot: number | undefined): void => {
      if (
        slot === undefined
        || slot < 0
        || slot >= carrierWires.length
        || inserted.has(slot)
      ) return
      inserted.add(slot)
      endpoints.push({
        node: input.node,
        port: { kind: 'free', index: slot },
      })
    }
    for (const endpoint of wire.endpoints) {
      if (endpoint.node === output.node) {
        insertSlot(
          endpoint.port.kind === 'free'
            ? producerMapping[endpoint.port.index]
            : undefined,
        )
        continue
      }
      if (endpoint.node === input.node && endpoint.port.kind === 'free') {
        insertSlot(consumerMapping[endpoint.port.index])
        continue
      }
      endpoints.push(endpoint)
    }
    for (const slot of slotsByWire.get(candidateId) ?? []) {
      if (!inserted.has(slot)) {
        endpoints.push({
          node: input.node,
          port: { kind: 'free', index: slot },
        })
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
