import type { Term } from '../term/term'
import type { Diagram, Endpoint, NodeId, Region, RegionId, DiagramNode, Wire, WireId } from './diagram'
import { mkDiagram, portKey, requiredPorts } from './diagram'

/**
 * Ergonomic incremental construction with deterministic ids (r0, r1, …; n0, …;
 * w0, …; auto-wires continue the w-counter). On build(), every port not
 * attached by an explicit wire receives a fresh singleton wire scoped at its
 * node's own region — establishing the partition invariant mechanically.
 * build() validates via mkDiagram and does not mutate builder state, so it is
 * repeatable.
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

  bubble(parent: RegionId, arity: number): RegionId {
    const id = `r${this.regionCount++}`
    this.regions[id] = { kind: 'bubble', parent, arity }
    return id
  }

  termNode(region: RegionId, term: Term): NodeId {
    const id = `n${this.nodeCount++}`
    this.nodes[id] = { kind: 'term', region, term }
    return id
  }

  atom(region: RegionId, binder: RegionId): NodeId {
    const id = `n${this.nodeCount++}`
    this.nodes[id] = { kind: 'atom', region, binder }
    return id
  }

  wire(scope: RegionId, endpoints: Endpoint[]): WireId {
    const id = `w${this.wireCount++}`
    this.wires[id] = { scope, endpoints }
    return id
  }

  build(): Diagram {
    const attached = new Map<NodeId, Set<string>>()
    for (const w of Object.values(this.wires)) {
      for (const ep of w.endpoints) {
        let byPort = attached.get(ep.node)
        if (byPort === undefined) {
          byPort = new Set()
          attached.set(ep.node, byPort)
        }
        byPort.add(portKey(ep.port))
      }
    }
    const autoWires: Record<WireId, Wire> = {}
    let auto = this.wireCount
    for (const [id, n] of Object.entries(this.nodes)) {
      for (const q of requiredPorts({ regions: this.regions }, n)) {
        if (attached.get(id)?.has(portKey(q)) !== true) {
          autoWires[`w${auto++}`] = { scope: n.region, endpoints: [{ node: id, port: q }] }
        }
      }
    }
    return mkDiagram({
      root: this.root,
      regions: { ...this.regions },
      nodes: { ...this.nodes },
      wires: { ...this.wires, ...autoWires },
    })
  }
}
