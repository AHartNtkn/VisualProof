import type {
  Diagram,
  DiagramNormalization,
  Endpoint,
  IdentityDiagramNode,
  NodeId,
  Wire,
  WireId,
} from '../diagram'
import { validateRawDiagram } from '../diagram'

function identityIds(diagram: Diagram): NodeId[] {
  return Object.keys(diagram.nodes)
    .filter((id) => diagram.nodes[id]!.kind === 'identity')
    .sort()
}

function incidentWireIds(diagram: Diagram, nodeId: NodeId): WireId[] {
  return Object.entries(diagram.wires)
    .filter(([, wire]) => wire.endpoints.some((endpoint) => endpoint.node === nodeId))
    .map(([wireId]) => wireId)
    .sort()
}

function rebuild(
  diagram: Diagram,
  nodes: Record<NodeId, Diagram['nodes'][NodeId]>,
  wires: Record<WireId, Wire>,
): Diagram {
  return {
    root: diagram.root,
    regions: diagram.regions,
    nodes,
    wires,
  }
}

function dropIdentity(diagram: Diagram, nodeId: NodeId): Diagram {
  const nodes = { ...diagram.nodes }
  delete nodes[nodeId]
  const wires: Record<WireId, Wire> = {}
  for (const [wireId, wire] of Object.entries(diagram.wires)) {
    wires[wireId] = {
      scope: wire.scope,
      sig: wire.sig,
      endpoints: wire.endpoints.filter((endpoint) => endpoint.node !== nodeId),
    }
  }
  return rebuild(diagram, nodes, wires)
}

function redirectImage(
  image: Map<WireId, WireId | undefined>,
  absorbed: ReadonlySet<WireId>,
  survivor: WireId,
): void {
  for (const [original, current] of image) {
    if (current !== undefined && absorbed.has(current)) {
      image.set(original, survivor)
    }
  }
}

function collapseIdentity(
  diagram: Diagram,
  nodeId: NodeId,
  image: Map<WireId, WireId | undefined>,
  survivor: WireId,
): Diagram {
  const incident = incidentWireIds(diagram, nodeId)
  const absorbed = new Set(incident.filter((wireId) => wireId !== survivor))
  const endpoints: Endpoint[] = []
  for (const wireId of incident) {
    for (const endpoint of diagram.wires[wireId]!.endpoints) {
      if (endpoint.node !== nodeId) endpoints.push(endpoint)
    }
  }

  const nodes = { ...diagram.nodes }
  delete nodes[nodeId]
  const wires = { ...diagram.wires }
  const survivingWire = diagram.wires[survivor]!
  wires[survivor] = {
    scope: survivingWire.scope,
    sig: survivingWire.sig,
    endpoints,
  }
  for (const wireId of absorbed) delete wires[wireId]
  redirectImage(image, absorbed, survivor)
  return rebuild(diagram, nodes, wires)
}

function fuseIdentities(
  diagram: Diagram,
  survivorId: NodeId,
  absorbedId: NodeId,
): Diagram {
  const survivor = diagram.nodes[survivorId] as IdentityDiagramNode
  const incident = [...new Set([
    ...incidentWireIds(diagram, survivorId),
    ...incidentWireIds(diagram, absorbedId),
  ])].sort()
  const incidenceIndex = new Map(incident.map((wireId, index) => [wireId, index]))

  const nodes = { ...diagram.nodes }
  nodes[survivorId] = {
    kind: 'identity',
    region: survivor.region,
    sig: survivor.sig,
    arity: incident.length,
  }
  delete nodes[absorbedId]

  const wires: Record<WireId, Wire> = {}
  for (const [wireId, wire] of Object.entries(diagram.wires)) {
    const index = incidenceIndex.get(wireId)
    const endpoints = wire.endpoints.filter(
      (endpoint) => endpoint.node !== survivorId && endpoint.node !== absorbedId,
    )
    if (index !== undefined) {
      endpoints.push({
        node: survivorId,
        port: { kind: 'identity', index },
      })
    }
    wires[wireId] = { scope: wire.scope, sig: wire.sig, endpoints }
  }
  return rebuild(diagram, nodes, wires)
}

function normalizeOneIdentity(
  diagram: Diagram,
  image: Map<WireId, WireId | undefined>,
): Diagram | null {
  const ids = identityIds(diagram)

  for (const nodeId of ids) {
    if (incidentWireIds(diagram, nodeId).length === 1) {
      return dropIdentity(diagram, nodeId)
    }
  }

  for (const nodeId of ids) {
    const node = diagram.nodes[nodeId] as IdentityDiagramNode
    const incident = incidentWireIds(diagram, nodeId)
    if (incident.every((wireId) => diagram.wires[wireId]!.scope === node.region)) {
      return collapseIdentity(diagram, nodeId, image, incident[0]!)
    }
  }

  const incidentByNode = new Map(ids.map((nodeId) => [
    nodeId,
    new Set(incidentWireIds(diagram, nodeId)),
  ]))
  for (let leftIndex = 0; leftIndex < ids.length; leftIndex++) {
    const leftId = ids[leftIndex]!
    const left = diagram.nodes[leftId] as IdentityDiagramNode
    const leftWires = incidentByNode.get(leftId)!
    for (let rightIndex = leftIndex + 1; rightIndex < ids.length; rightIndex++) {
      const rightId = ids[rightIndex]!
      const right = diagram.nodes[rightId] as IdentityDiagramNode
      if (left.region !== right.region) continue
      if ([...incidentByNode.get(rightId)!].some((wireId) => leftWires.has(wireId))) {
        return fuseIdentities(diagram, leftId, rightId)
      }
    }
  }

  return null
}

function freezeImage(
  image: Map<WireId, WireId | undefined>,
  diagram: Diagram,
): ReadonlyMap<WireId, WireId | undefined> {
  const frozen = new Map<WireId, WireId | undefined>()
  for (const [original, current] of image) {
    let resolved = current
    const seen = new Set<WireId>()
    while (resolved !== undefined && !seen.has(resolved)) {
      seen.add(resolved)
      const next = image.get(resolved)
      if (next === undefined || next === resolved) break
      resolved = next
    }
    image.set(original, resolved)
    frozen.set(
      original,
      resolved !== undefined && diagram.wires[resolved] !== undefined ? resolved : undefined,
    )
  }
  return Object.freeze(frozen)
}

/**
 * The sole identity canonicalizer. Raw validity is established before any
 * rewrite; every deterministic rewrite is revalidated before the next step.
 */
export function normalizeIdentities(raw: Diagram): DiagramNormalization {
  let current = validateRawDiagram(raw)
  const image = new Map<WireId, WireId | undefined>(
    Object.keys(current.wires).map((wireId) => [wireId, wireId]),
  )
  for (;;) {
    const next = normalizeOneIdentity(current, image)
    if (next === null) {
      return {
        diagram: current,
        wireImage: freezeImage(image, current),
      }
    }
    current = validateRawDiagram(next)
  }
}
