import type {
  Diagram,
  DiagramNode,
  Endpoint,
  NodeId,
  Region,
  RegionId,
  Wire,
  WireId,
} from './diagram'
import { mkDiagram, portKey, portSig, requiredPorts } from './diagram'
import type { RelSig, Sig } from './sig'
import { IOTA } from './sig'

/**
 * Incremental construction with deterministic region, node, and wire IDs.
 * build() attaches every still-free storage port to a fresh singleton wire,
 * then delegates to the eager canonical diagram constructor.
 */
export class DiagramBuilder {
  readonly root: RegionId = 'r0'
  private regionCount = 1
  private nodeCount = 0
  private wireCount = 0
  private readonly regions: Record<RegionId, Region> = { r0: { kind: 'sheet' } }
  private readonly nodes: Record<NodeId, DiagramNode> = {}
  private readonly wires: Record<WireId, Wire> = {}

  cut(parent: RegionId): RegionId {
    const id = `r${this.regionCount++}`
    this.regions[id] = { kind: 'cut', parent }
    return id
  }

  atom(region: RegionId, sig: RelSig): NodeId {
    const id = `n${this.nodeCount++}`
    this.nodes[id] = { kind: 'atom', region, sig }
    return id
  }

  ref(region: RegionId, defId: string, sig: RelSig): NodeId {
    const id = `n${this.nodeCount++}`
    this.nodes[id] = { kind: 'ref', region, defId, sig }
    return id
  }

  identity(region: RegionId, sig: Sig, arity: number): NodeId {
    const id = `n${this.nodeCount++}`
    this.nodes[id] = { kind: 'identity', region, sig, arity }
    return id
  }

  /**
   * Generic wire constructor. IOTA remains the useful default for ordinary
   * individual arguments and identities; relational ports pass their sig.
   */
  wire(scope: RegionId, endpoints: Endpoint[], sig: Sig = IOTA): WireId {
    const id = `w${this.wireCount++}`
    this.wires[id] = { scope, sig, endpoints }
    return id
  }

  /** Create an endpoint-free relational wire for later attachment. */
  relWire(scope: RegionId, sig: RelSig): WireId {
    const id = `w${this.wireCount++}`
    this.wires[id] = { scope, sig, endpoints: [] }
    return id
  }

  build(): Diagram {
    const attached = new Map<NodeId, Set<string>>()
    for (const wire of Object.values(this.wires)) {
      for (const endpoint of wire.endpoints) {
        let ports = attached.get(endpoint.node)
        if (ports === undefined) {
          ports = new Set()
          attached.set(endpoint.node, ports)
        }
        ports.add(portKey(endpoint.port))
      }
    }

    const automaticWires: Record<WireId, Wire> = {}
    let nextWire = this.wireCount
    for (const [nodeId, node] of Object.entries(this.nodes)) {
      for (const port of requiredPorts(node)) {
        if (attached.get(nodeId)?.has(portKey(port)) !== true) {
          automaticWires[`w${nextWire++}`] = {
            scope: node.region,
            sig: portSig(node, port),
            endpoints: [{ node: nodeId, port }],
          }
        }
      }
    }

    return mkDiagram({
      root: this.root,
      regions: { ...this.regions },
      nodes: { ...this.nodes },
      wires: { ...this.wires, ...automaticWires },
    })
  }
}
