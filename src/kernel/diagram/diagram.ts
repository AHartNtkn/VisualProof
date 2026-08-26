import type { Term } from '../term/term'
import { assertWellFormedTerm } from '../term/term'
import type { Sig, RelSig } from './sig'
import { assertWellFormedSig, IOTA, sigEquals, sigKey } from './sig'

export type RegionId = string
export type NodeId = string
export type WireId = string

export type Region =
  | { readonly kind: 'sheet' }
  | { readonly kind: 'cut'; readonly parent: RegionId }

export type IdentityDiagramNode = {
  readonly kind: 'identity'
  readonly region: RegionId
  readonly sig: Sig
  /**
   * Any natural. 0 is a typed point of existence (∃x:σ.⊤); 1 is a
   * reflexive end holding an incidence — a pin when that is its whole job;
   * ≥2 asserts its wires' values all equal.
   */
  readonly arity: number
}

export type TermDiagramNode = {
  readonly kind: 'term'
  readonly region: RegionId
  readonly term: Term
  readonly freeArity: number
}

export type DiagramNode =
  | TermDiagramNode
  | { readonly kind: 'atom'; readonly region: RegionId; readonly sig: RelSig }
  | { readonly kind: 'ref'; readonly region: RegionId; readonly defId: string; readonly sig: RelSig }
  | IdentityDiagramNode

export type Port =
  | { readonly kind: 'output' }
  | { readonly kind: 'free'; readonly index: number }
  | { readonly kind: 'arg'; readonly index: number }
  | { readonly kind: 'head' }
  | { readonly kind: 'identity'; readonly index: number }

export type Endpoint = { readonly node: NodeId; readonly port: Port }

/**
 * One wire is one existentially scoped value of a fixed signature. Where its
 * quantifier lives is DERIVED: the deepest common ancestor of its incidence
 * regions (endpoints, plus boundary entries at the root) — see
 * `derivedScope`. Every attached port must accept the wire's signature, and
 * every wire has at least two ends: a wire end is a node, so a one-incidence
 * wire is a line from a point to nowhere and is unrepresentable (the two-end
 * floor; derived-scope identity rules spec §1).
 */
export type Wire = {
  readonly sig: Sig
  readonly endpoints: readonly Endpoint[]
}

export type Diagram = {
  readonly root: RegionId
  readonly regions: Readonly<Record<RegionId, Region>>
  readonly nodes: Readonly<Record<NodeId, DiagramNode>>
  readonly wires: Readonly<Record<WireId, Wire>>
}

export type DiagramParts = {
  readonly root: RegionId
  readonly regions: Record<RegionId, Region>
  readonly nodes?: Record<NodeId, DiagramNode>
  readonly wires?: Record<WireId, Wire>
}

export class DiagramError extends Error {
  constructor(message: string) {
    super(message)
    this.name = 'DiagramError'
  }
}

export function portKey(port: Port): string {
  switch (port.kind) {
    case 'output': return 'out'
    case 'free': return `f:${port.index}`
    case 'arg': return `a:${port.index}`
    case 'head': return 'hd'
    case 'identity': return `i:${port.index}`
  }
}

/**
 * Semantic port position of a wire endpoint. Identity incidence indices are
 * deliberately erased: their incident-wire multiset, not their storage
 * index, is the structure that identity carries — see `requiredPorts`'s
 * `identity` case, whose ports are storage addresses only.
 *
 * Every caller feeds endpoints of a validated diagram, where a node only
 * ever carries the port kinds `requiredPorts` lists for it — a mismatched
 * port kind is a structural invariant violation, not reachable input, so it
 * throws loudly rather than returning a sentinel a caller could silently
 * compare against.
 */
export function endpointPositionKey(diagram: Diagram, endpoint: Endpoint): string {
  const node = diagram.nodes[endpoint.node]!
  switch (node.kind) {
    case 'term':
      if (endpoint.port.kind === 'output') return 'out'
      if (endpoint.port.kind === 'free') return `f:${endpoint.port.index}`
      throw new DiagramError(`term node cannot carry port kind '${endpoint.port.kind}'`)
    case 'atom':
      if (endpoint.port.kind === 'head') return 'hd'
      if (endpoint.port.kind === 'arg') return `a:${endpoint.port.index}`
      throw new DiagramError(`atom node cannot carry port kind '${endpoint.port.kind}'`)
    case 'ref':
      if (endpoint.port.kind === 'arg') return `a:${endpoint.port.index}`
      throw new DiagramError(`ref node cannot carry port kind '${endpoint.port.kind}'`)
    case 'identity':
      if (endpoint.port.kind === 'identity') return 'i'
      throw new DiagramError(`identity node cannot carry port kind '${endpoint.port.kind}'`)
  }
}

/** The exact storage ports a node must have attached. */
export function requiredPorts(node: DiagramNode): Port[] {
  switch (node.kind) {
    case 'term':
      return [
        { kind: 'output' },
        ...Array.from(
          { length: node.freeArity },
          (_, index): Port => ({ kind: 'free', index }),
        ),
      ]
    case 'atom':
      return [
        { kind: 'head' },
        ...node.sig.args.map((_, index): Port => ({ kind: 'arg', index })),
      ]
    case 'ref':
      return node.sig.args.map((_, index): Port => ({ kind: 'arg', index }))
    case 'identity':
      return Array.from(
        { length: node.arity },
        (_, index): Port => ({ kind: 'identity', index }),
      )
  }
}

/** The signature accepted by one concrete storage port. */
export function portSig(node: DiagramNode, port: Port): Sig {
  switch (node.kind) {
    case 'term':
      if (port.kind === 'output') return IOTA
      if (
        port.kind === 'free'
        && Number.isSafeInteger(port.index)
        && port.index >= 0
        && port.index < node.freeArity
      ) {
        return IOTA
      }
      break
    case 'atom':
      if (port.kind === 'head') return node.sig
      if (port.kind === 'arg') {
        const sig = node.sig.args[port.index]
        if (sig !== undefined) return sig
      }
      break
    case 'ref':
      if (port.kind === 'arg') {
        const sig = node.sig.args[port.index]
        if (sig !== undefined) return sig
      }
      break
    case 'identity':
      if (
        port.kind === 'identity'
        && Number.isSafeInteger(port.index)
        && port.index >= 0
        && port.index < node.arity
      ) {
        return node.sig
      }
      break
  }
  throw new DiagramError(`node of kind '${node.kind}' has no port '${portKey(port)}'`)
}

function fail(message: string): never {
  throw new DiagramError(message)
}

/**
 * Validate and freeze a graph. `boundary` lists the ordered boundary
 * incidences of an open diagram (repeats allowed): each entry counts as one
 * end of its wire at the root, so a closed diagram (no boundary) requires
 * two endpoints per wire while an open one may expose a wire instead.
 */
export function validateRawDiagram(
  raw: Diagram,
  boundary: readonly WireId[] = [],
): Diagram {
  const rootId = raw.root
  const regions = raw.regions
  const nodes = raw.nodes
  const wires = raw.wires

  const root = regions[rootId] ?? fail(`root region '${rootId}' does not exist`)
  if (root.kind !== 'sheet') {
    fail(`root region '${rootId}' must be a sheet, got '${root.kind}'`)
  }

  for (const [id, region] of Object.entries(regions)) {
    if (region.kind === 'sheet' && id !== rootId) {
      fail(`region '${id}' is a second sheet; only the root may be a sheet`)
    }
    if (region.kind === 'cut' && regions[region.parent] === undefined) {
      fail(`region '${id}' has missing parent '${region.parent}'`)
    }
  }

  for (const id of Object.keys(regions)) {
    const seen = new Set<RegionId>()
    let current = id
    for (;;) {
      if (seen.has(current)) {
        fail(`region parent chain from '${id}' contains a cycle at '${current}'`)
      }
      seen.add(current)
      const region = regions[current]!
      if (region.kind === 'sheet') break
      current = region.parent
    }
  }

  const assertNodeSig = (id: NodeId, kind: DiagramNode['kind'], sig: Sig): void => {
    try {
      assertWellFormedSig(sig)
    } catch (error) {
      fail(`${kind} node '${id}' sig: ${error instanceof Error ? error.message : String(error)}`)
    }
  }

  for (const [id, node] of Object.entries(nodes)) {
    if (regions[node.region] === undefined) {
      fail(`node '${id}' is in missing region '${node.region}'`)
    }
    switch (node.kind) {
      case 'term':
        if (!Number.isSafeInteger(node.freeArity) || node.freeArity < 0) {
          fail(`term node '${id}' freeArity must be a natural number, got '${String(node.freeArity)}'`)
        }
        try {
          assertWellFormedTerm(node.term, node.freeArity)
        } catch (error) {
          fail(`term node '${id}' term: ${error instanceof Error ? error.message : String(error)}`)
        }
        break
      case 'atom':
      case 'ref':
        assertNodeSig(id, node.kind, node.sig)
        if (node.sig.kind !== 'rel') {
          fail(`${node.kind} node '${id}' sig must be a relation signature, got '${sigKey(node.sig)}'`)
        }
        break
      case 'identity':
        assertNodeSig(id, node.kind, node.sig)
        if (!Number.isSafeInteger(node.arity) || node.arity < 0) {
          fail(`identity node '${id}' arity must be a natural number, got '${String(node.arity)}'`)
        }
        break
      default:
        node satisfies never
        fail(`node '${id}' has an unrecognized kind`)
    }
  }

  const boundaryEnds = new Map<WireId, number>()
  for (const wireId of boundary) {
    if (wires[wireId] === undefined) {
      fail(`boundary wire '${wireId}' does not exist`)
    }
    boundaryEnds.set(wireId, (boundaryEnds.get(wireId) ?? 0) + 1)
  }

  const portsByNode = new Map<NodeId, Port[]>()
  for (const [id, node] of Object.entries(nodes)) {
    portsByNode.set(id, requiredPorts(node))
  }

  const attached = new Map<NodeId, Map<string, WireId>>()
  for (const [wireId, wire] of Object.entries(wires)) {
    try {
      assertWellFormedSig(wire.sig)
    } catch (error) {
      fail(`wire '${wireId}' sig: ${error instanceof Error ? error.message : String(error)}`)
    }
    for (const endpoint of wire.endpoints) {
      const node = nodes[endpoint.node]
        ?? fail(`wire '${wireId}' endpoint references missing node '${endpoint.node}'`)
      const key = portKey(endpoint.port)
      const required = portsByNode.get(endpoint.node)!
      if (!required.some((candidate) => portKey(candidate) === key)) {
        fail(`wire '${wireId}' endpoint references non-existent port '${key}' of node '${endpoint.node}'`)
      }
      const expected = portSig(node, endpoint.port)
      if (!sigEquals(wire.sig, expected)) {
        fail(
          `wire '${wireId}' sig '${sigKey(wire.sig)}' does not match port '${key}' `
          + `of node '${endpoint.node}' expecting '${sigKey(expected)}'`,
        )
      }
      let byPort = attached.get(endpoint.node)
      if (byPort === undefined) {
        byPort = new Map()
        attached.set(endpoint.node, byPort)
      }
      const previous = byPort.get(key)
      if (previous !== undefined) {
        fail(previous === wireId
          ? `port '${key}' of node '${endpoint.node}' appears more than once in wire '${wireId}'`
          : `port '${key}' of node '${endpoint.node}' is attached to two wires ('${previous}' and '${wireId}')`)
      }
      byPort.set(key, wireId)
    }
    const ends = wire.endpoints.length + (boundaryEnds.get(wireId) ?? 0)
    if (ends < 2) {
      fail(
        `wire '${wireId}' has ${ends} end(s); every wire needs at least two — `
        + `a wire end is a node (attach it, or give it an identity point)`,
      )
    }
  }

  for (const nodeId of Object.keys(nodes)) {
    for (const port of portsByNode.get(nodeId)!) {
      if (attached.get(nodeId)?.get(portKey(port)) === undefined) {
        fail(`port '${portKey(port)}' of node '${nodeId}' is not attached to any wire`)
      }
    }
  }

  return Object.freeze({
    root: rootId,
    regions: Object.freeze({ ...regions }),
    nodes: Object.freeze({ ...nodes }),
    wires: Object.freeze({ ...wires }),
  })
}

function rawFromParts(parts: DiagramParts): Diagram {
  return {
    root: parts.root,
    regions: parts.regions,
    nodes: parts.nodes ?? {},
    wires: parts.wires ?? {},
  }
}

/** Canonical closed-diagram construction: validate and freeze. */
export function mkDiagram(parts: DiagramParts): Diagram {
  return validateRawDiagram(rawFromParts(parts))
}
