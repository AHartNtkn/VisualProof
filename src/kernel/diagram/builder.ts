import type { Term } from '../term/term'
import { freePorts } from '../term/term'
import type { Diagram, Endpoint, NodeId, Region, RegionId, DiagramNode, Wire, WireId } from './diagram'
import { mkDiagram, portKey, portSig, requiredPorts } from './diagram'
import type { RelSig, Sig } from './sig'
import { TERM } from './sig'

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

  termNode(region: RegionId, term: Term, declaredFreePorts: readonly string[] = freePorts(term)): NodeId {
    const id = `n${this.nodeCount++}`
    this.nodes[id] = { kind: 'term', region, term, freePorts: [...declaredFreePorts] }
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

  /**
   * Generic wire constructor. `sig` defaults to TERM since most manually
   * wired ports (term output/freeVar, atom/ref arg) accept TERM; a wire
   * touching an atom's head or a ref's arg on a relational sig must pass its
   * sig explicitly — mkDiagram enforces the match at every endpoint.
   */
  wire(scope: RegionId, endpoints: Endpoint[], sig: Sig = TERM): WireId {
    const id = `w${this.wireCount++}`
    this.wires[id] = { scope, sig, endpoints }
    return id
  }

  /**
   * An endpoint-free relational wire: a placeholder line of identity with no
   * attached ports yet, later bound by e.g. `spawnBoundRelationNode`.
   */
  relWire(scope: RegionId, sig: RelSig): WireId {
    const id = `w${this.wireCount++}`
    this.wires[id] = { scope, sig, endpoints: [] }
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
      for (const q of requiredPorts(n)) {
        if (attached.get(id)?.has(portKey(q)) !== true) {
          autoWires[`w${auto++}`] = { scope: n.region, sig: portSig(n, q), endpoints: [{ node: id, port: q }] }
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
