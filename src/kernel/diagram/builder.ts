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
import { DiagramError, mkDiagram, portKey, portSig, requiredPorts, validateRawDiagram } from './diagram'
import type { DiagramWithBoundary } from './boundary'
import { mkDiagramWithBoundary } from './boundary'
import type { RelSig, Sig } from './sig'
import { IOTA } from './sig'

/**
 * Incremental construction with deterministic region, node, and wire IDs.
 * Wires carry no scope — where a quantifier lives is derived from
 * incidences, so authors place identity points and pins instead of naming
 * regions on wires. build() completes the picture mechanically: every
 * still-free storage port gets a fresh wire ending in a pin at the node's
 * region, and every explicitly built wire left with a single end gets a pin
 * at that end's region (the free tip drawn as the node it is). A wire with
 * no ends at all cannot be completed — the author must say where its
 * quantifier lives (use point()/pin()).
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

  /** A nullary identity: a typed point of existence (∃x:σ.⊤) at `region`. */
  point(region: RegionId, sig: Sig = IOTA): NodeId {
    return this.identity(region, sig, 0)
  }

  /**
   * Attach a fresh unary identity at `region` to an existing wire — the pin
   * that holds the wire's quantifier at least as high as `region`.
   */
  pin(wire: WireId, region: RegionId): NodeId {
    const existing = this.wires[wire]
    if (existing === undefined) throw new DiagramError(`unknown wire '${wire}'`)
    const node = this.identity(region, existing.sig, 1)
    this.wires[wire] = {
      sig: existing.sig,
      endpoints: [...existing.endpoints, { node, port: { kind: 'identity', index: 0 } }],
    }
    return node
  }

  /**
   * Generic wire constructor. IOTA remains the useful default for ordinary
   * individual arguments and identities; relational ports pass their sig.
   */
  wire(endpoints: Endpoint[], sig: Sig = IOTA): WireId {
    const id = `w${this.wireCount++}`
    this.wires[id] = { sig, endpoints }
    return id
  }

  /** Create a not-yet-attached relational wire for later endpoints. */
  relWire(sig: RelSig): WireId {
    const id = `w${this.wireCount++}`
    this.wires[id] = { sig, endpoints: [] }
    return id
  }

  private completed(boundary: readonly WireId[]): {
    nodes: Record<NodeId, DiagramNode>
    wires: Record<WireId, Wire>
  } {
    const nodes: Record<NodeId, DiagramNode> = { ...this.nodes }
    const wires: Record<WireId, Wire> = { ...this.wires }
    let nextNode = this.nodeCount
    let nextWire = this.wireCount

    const mintPin = (sig: Sig, region: RegionId): Endpoint => {
      const node = `n${nextNode++}`
      nodes[node] = { kind: 'identity', region, sig, arity: 1 }
      return { node, port: { kind: 'identity', index: 0 } }
    }

    const attached = new Map<NodeId, Set<string>>()
    for (const wire of Object.values(wires)) {
      for (const endpoint of wire.endpoints) {
        let ports = attached.get(endpoint.node)
        if (ports === undefined) {
          ports = new Set()
          attached.set(endpoint.node, ports)
        }
        ports.add(portKey(endpoint.port))
      }
    }

    for (const [nodeId, node] of Object.entries(this.nodes)) {
      for (const port of requiredPorts(node)) {
        if (attached.get(nodeId)?.has(portKey(port)) !== true) {
          const sig = portSig(node, port)
          wires[`w${nextWire++}`] = {
            sig,
            endpoints: [{ node: nodeId, port }, mintPin(sig, node.region)],
          }
        }
      }
    }

    const boundaryEnds = new Map<WireId, number>()
    for (const wireId of boundary) {
      boundaryEnds.set(wireId, (boundaryEnds.get(wireId) ?? 0) + 1)
    }
    for (const [wireId, wire] of Object.entries(wires)) {
      const ends = wire.endpoints.length + (boundaryEnds.get(wireId) ?? 0)
      if (ends >= 2) continue
      if (ends === 0) {
        throw new DiagramError(
          `wire '${wireId}' has no ends; say where its quantifier lives `
          + `(attach it, pin it, or use point() for a bare existential)`,
        )
      }
      const sole = wire.endpoints[0]
      const region = sole !== undefined
        ? nodes[sole.node]!.region
        : this.root
      wires[wireId] = {
        sig: wire.sig,
        endpoints: [...wire.endpoints, mintPin(wire.sig, region)],
      }
    }

    return { nodes, wires }
  }

  build(): Diagram {
    const { nodes, wires } = this.completed([])
    return mkDiagram({
      root: this.root,
      regions: { ...this.regions },
      nodes,
      wires,
    })
  }

  /** Build an open diagram: boundary entries count toward the two-end floor. */
  buildOpen(boundary: readonly WireId[]): DiagramWithBoundary {
    const { nodes, wires } = this.completed(boundary)
    return mkDiagramWithBoundary(
      validateRawDiagram({
        root: this.root,
        regions: { ...this.regions },
        nodes,
        wires,
      }, boundary),
      boundary,
    )
  }
}
