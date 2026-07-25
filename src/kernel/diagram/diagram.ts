import type { Term } from '../term/term'
import { freePorts, renameFreePorts, assertWellFormedTerm } from '../term/term'
import type { Sig, RelSig } from './sig'
import { IOTA, sigEquals, sigKey, assertWellFormedSig } from './sig'
// Type-only: `DiagramWithBoundary` payloads live on body nodes. This import is
// erased at runtime, so it introduces no cycle with boundary.ts (which imports
// runtime values from here).
import type { DiagramWithBoundary } from './boundary'

export type RegionId = string
export type NodeId = string
export type WireId = string

export type Region =
  | { readonly kind: 'sheet' }
  | { readonly kind: 'cut'; readonly parent: RegionId }

export type TermDiagramNode = {
  readonly kind: 'term'
  readonly region: RegionId
  readonly term: Term
  /** Ordered, authoritative interface. May contain names unused by `term`. */
  readonly freePorts: readonly string[]
}

export type DiagramNode =
  | TermDiagramNode
  | { readonly kind: 'atom'; readonly region: RegionId; readonly sig: RelSig }
  | { readonly kind: 'ref'; readonly region: RegionId; readonly defId: string; readonly sig: RelSig }
  | { readonly kind: 'body'; readonly region: RegionId; readonly sig: RelSig; readonly content: DiagramWithBoundary }

/** Construction-only input. Validated Diagram values always materialize `freePorts`. */
export type DiagramNodeInput =
  | Omit<TermDiagramNode, 'freePorts'> & { readonly freePorts?: readonly string[] }
  | Exclude<DiagramNode, TermDiagramNode>

export type Port =
  | { readonly kind: 'output' }
  | { readonly kind: 'freeVar'; readonly name: string }
  | { readonly kind: 'arg'; readonly index: number }
  | { readonly kind: 'head' }

export type Endpoint = { readonly node: NodeId; readonly port: Port }

/**
 * One wire = one line of identity = one existentially scoped individual of a
 * fixed sort. `sig` is the sort every attached port must accept.
 */
export type Wire = { readonly scope: RegionId; readonly sig: Sig; readonly endpoints: readonly Endpoint[] }

export type Diagram = {
  readonly root: RegionId
  readonly regions: Readonly<Record<RegionId, Region>>
  readonly nodes: Readonly<Record<NodeId, DiagramNode>>
  readonly wires: Readonly<Record<WireId, Wire>>
}

export class DiagramError extends Error {
  constructor(message: string) {
    super(message)
    this.name = 'DiagramError'
  }
}

export function portKey(p: Port): string {
  switch (p.kind) {
    case 'output': return 'out'
    case 'freeVar': return `v:${p.name}`
    case 'arg': return `a:${p.index}`
    case 'head': return 'hd'
  }
}

/**
 * The exact port set a node must have attached. Context-free: every node's port
 * shape is read from its own inline data.
 * - term: output plus one freeVar port per declared free port (declared order).
 * - atom: head plus arg 0..sig.args.length-1.
 * - ref: arg 0..sig.args.length-1 (no head, no output).
 * - body: output plus one freeVar port p0..p(k-1) per parameter, where the
 *   parameters are the boundary wires past the arg stubs
 *   (k = boundary.length - sig.args.length).
 */
export function requiredPorts(node: DiagramNode): Port[] {
  switch (node.kind) {
    case 'term':
      return [
        { kind: 'output' },
        ...node.freePorts.map((name): Port => ({ kind: 'freeVar', name })),
      ]
    case 'atom':
      return [
        { kind: 'head' },
        ...node.sig.args.map((_, index): Port => ({ kind: 'arg', index })),
      ]
    case 'ref':
      return node.sig.args.map((_, index): Port => ({ kind: 'arg', index }))
    case 'body': {
      const paramCount = node.content.boundary.length - node.sig.args.length
      return [
        { kind: 'output' },
        ...Array.from({ length: paramCount }, (_, j): Port => ({ kind: 'freeVar', name: `p${j}` })),
      ]
    }
  }
}

/**
 * The sort a port accepts.
 * - term node: every port is `IOTA` (output and each declared freeVar).
 * - atom: head accepts `node.sig`; arg i accepts `node.sig.args[i]`.
 * - ref: arg i accepts `node.sig.args[i]` (no head/output).
 * - body: output accepts `node.sig`; freeVar pj accepts the sig of the
 *   parameter boundary wire `content.boundary[argCount + j]`.
 *
 * Throws `DiagramError` for a port the node does not have.
 */
export function portSig(node: DiagramNode, port: Port): Sig {
  switch (node.kind) {
    case 'term':
      if (port.kind === 'output') return IOTA
      if (port.kind === 'freeVar' && node.freePorts.includes(port.name)) return IOTA
      break
    case 'atom':
      if (port.kind === 'head') return node.sig
      if (port.kind === 'arg') {
        const s = node.sig.args[port.index]
        if (s !== undefined) return s
      }
      break
    case 'ref':
      if (port.kind === 'arg') {
        const s = node.sig.args[port.index]
        if (s !== undefined) return s
      }
      break
    case 'body': {
      if (port.kind === 'output') return node.sig
      if (port.kind === 'freeVar') {
        const argCount = node.sig.args.length
        const paramCount = node.content.boundary.length - argCount
        for (let j = 0; j < paramCount; j++) {
          if (port.name === `p${j}`) {
            const wid = node.content.boundary[argCount + j]!
            const w = node.content.diagram.wires[wid]
            if (w === undefined) {
              throw new DiagramError(`body node parameter wire '${wid}' is missing from content`)
            }
            return w.sig
          }
        }
      }
      break
    }
  }
  throw new DiagramError(`node of kind '${node.kind}' has no port '${portKey(port)}'`)
}

/**
 * Free-port names are never semantic: every term node's free ports are
 * renamed to s0, s1, … in first-occurrence order, and the freeVar endpoints
 * of its wires are rewritten through the same per-node map — one simultaneous
 * pass, so swaps like {s0→s1, s1→s0} cannot cascade. Runs after term
 * well-formedness checks (renaming presupposes meaningful names) and before
 * port validation, so all downstream invariants hold over canonical names.
 *
 * Only term nodes carry renamable free ports. Atom, ref, and body nodes are
 * returned untouched; body freeVar ports are already canonical `p0…p(k-1)` by
 * construction and are validated (not renamed) by the port-membership check.
 *
 * An endpoint whose name is not an original free of its node is left for the
 * port-membership check to reject — except when it spells a canonical name
 * the rename is about to assign to a DIFFERENT port, where waiting would
 * silently alias it; that case is rejected here with the same vocabulary.
 * Already-canonical nodes and untouched wires keep their input objects.
 */
function canonicalizeFreePorts(
  nodes: Record<NodeId, DiagramNode>,
  wires: Record<WireId, Wire>,
): { nodes: Record<NodeId, DiagramNode>; wires: Record<WireId, Wire> } {
  const renames = new Map<NodeId, ReadonlyMap<string, string>>()
  let nodesChanged = false
  const nodesOut: Record<NodeId, DiagramNode> = {}
  // Return-typed switch (no default): a new node kind forces a decision here.
  const canonicalizeNode = (id: NodeId, n: DiagramNode): DiagramNode => {
    switch (n.kind) {
      case 'atom':
        return n
      case 'ref':
        return n
      case 'body':
        // Parameter freeVar ports are canonical p0… by construction.
        return n
      case 'term': {
        const map = new Map<string, string>()
        let identity = true
        for (const [i, name] of n.freePorts.entries()) {
          const to = `s${i}`
          map.set(name, to)
          if (name !== to) identity = false
        }
        renames.set(id, map)
        if (identity) return n
        nodesChanged = true
        return {
          kind: 'term',
          region: n.region,
          term: renameFreePorts(n.term, map),
          freePorts: n.freePorts.map((_, i) => `s${i}`),
        }
      }
    }
  }
  for (const [id, n] of Object.entries(nodes)) {
    nodesOut[id] = canonicalizeNode(id, n)
  }
  let wiresChanged = false
  const wiresOut: Record<WireId, Wire> = {}
  for (const [wid, w] of Object.entries(wires)) {
    let epsChanged = false
    const endpoints = w.endpoints.map((ep): Endpoint => {
      if (ep.port.kind !== 'freeVar') return ep
      const map = renames.get(ep.node) // undefined for atom/ref/body and missing nodes: validation rejects those endpoints
      if (map === undefined) return ep
      const to = map.get(ep.port.name)
      if (to === undefined) {
        for (const assigned of map.values()) {
          if (assigned === ep.port.name) {
            throw new DiagramError(`wire '${wid}' endpoint references non-existent port 'v:${ep.port.name}' of node '${ep.node}'`)
          }
        }
        return ep
      }
      if (to === ep.port.name) return ep
      epsChanged = true
      return { node: ep.node, port: { kind: 'freeVar', name: to } }
    })
    if (!epsChanged) {
      wiresOut[wid] = w
      continue
    }
    wiresOut[wid] = { scope: w.scope, sig: w.sig, endpoints }
    wiresChanged = true
  }
  return {
    nodes: nodesChanged ? nodesOut : nodes,
    wires: wiresChanged ? wiresOut : wires,
  }
}

function ancestorOrEqualRaw(regions: Readonly<Record<RegionId, Region>>, anc: RegionId, desc: RegionId): boolean {
  let cur: RegionId = desc
  for (;;) {
    if (cur === anc) return true
    const r = regions[cur]
    if (r === undefined || r.kind === 'sheet') return false
    cur = r.parent
  }
}

/**
 * The single validating constructor. Checks, in order: root is the unique
 * sheet; the parent graph is a tree rooted there; node regions and inline
 * signatures are valid (atom/ref/body sigs are relation signatures; body
 * content is coherent with the node sig); every wire sig is well-formed and
 * matches the sort of each port it attaches to; wire scopes enclose every
 * endpoint; and the wire endpoint sets exactly partition the set of all
 * required ports. Throws DiagramError with a specific message on the first
 * violation found.
 */
export function mkDiagram(parts: {
  root: RegionId
  regions: Record<RegionId, Region>
  nodes?: Record<NodeId, DiagramNodeInput>
  wires?: Record<WireId, Wire>
}): Diagram {
  const { root: rootId } = parts
  const regions = parts.regions
  const inputNodes = parts.nodes ?? {}
  const nodes: Record<NodeId, DiagramNode> = {}
  const wires = parts.wires ?? {}
  const fail = (msg: string): never => { throw new DiagramError(msg) }

  const root = regions[rootId] ?? fail(`root region '${rootId}' does not exist`)
  if (root.kind !== 'sheet') fail(`root region '${rootId}' must be a sheet, got '${root.kind}'`)

  for (const [id, r] of Object.entries(regions)) {
    if (r.kind === 'sheet' && id !== rootId) {
      fail(`region '${id}' is a second sheet; only the root may be a sheet`)
    }
    if (r.kind !== 'sheet' && regions[r.parent] === undefined) {
      fail(`region '${id}' has missing parent '${r.parent}'`)
    }
  }

  for (const id of Object.keys(regions)) {
    const seen = new Set<RegionId>()
    let cur = id
    for (;;) {
      if (seen.has(cur)) fail(`region parent chain from '${id}' contains a cycle at '${cur}'`)
      seen.add(cur)
      const r = regions[cur]!
      if (r.kind === 'sheet') break
      cur = r.parent
    }
  }

  const assertRelSig = (id: NodeId, kindLabel: string, sig: RelSig): void => {
    try {
      assertWellFormedSig(sig)
    } catch (e) {
      fail(`${kindLabel} node '${id}' sig: ${e instanceof Error ? e.message : String(e)}`)
    }
    if (sig.kind !== 'rel') fail(`${kindLabel} node '${id}' sig must be a relation signature, got '${sigKey(sig)}'`)
  }

  for (const [id, n] of Object.entries(inputNodes)) {
    if (regions[n.region] === undefined) fail(`node '${id}' is in missing region '${n.region}'`)
    switch (n.kind) {
      case 'term': {
        try {
          assertWellFormedTerm(n.term)
        } catch (e) {
          fail(`node '${id}' term: ${e instanceof Error ? e.message : String(e)}`)
        }
        const declared = n.freePorts ?? freePorts(n.term)
        const seen = new Set<string>()
        for (const name of declared) {
          if (typeof name !== 'string' || name.length === 0) {
            fail(`node '${id}' free port names must be nonempty strings`)
          }
          if (seen.has(name)) fail(`node '${id}' free port names must be unique; repeated '${name}'`)
          seen.add(name)
        }
        for (const name of freePorts(n.term)) {
          if (!seen.has(name)) fail(`node '${id}' free-port interface does not declare term port '${name}'`)
        }
        nodes[id] = n.freePorts !== undefined && Object.isFrozen(n.freePorts)
          ? n as TermDiagramNode
          : {
              kind: 'term',
              region: n.region,
              term: n.term,
              freePorts: Object.freeze([...declared]),
            }
        break
      }
      case 'atom':
        assertRelSig(id, 'atom', n.sig)
        nodes[id] = n
        break
      case 'ref':
        // Context-free: sig is stored inline and validated here; defId
        // resolution (exists? sig agrees?) is the rules' / verifyTheory's job.
        assertRelSig(id, 'ref', n.sig)
        nodes[id] = n
        break
      case 'body': {
        assertRelSig(id, 'body', n.sig)
        const argCount = n.sig.args.length
        const content = n.content
        const b = content.boundary
        if (b.length < argCount) {
          fail(`body node '${id}' boundary length ${b.length} is shorter than sig arity ${argCount}`)
        }
        // Content is a frozen Diagram, valid by construction (same trust model
        // as any Diagram value); we only re-establish the coherence layer that
        // makes portSig well-defined: boundary wires exist, are root-scoped,
        // and the arg stubs carry the sig's argument sorts.
        for (let i = 0; i < b.length; i++) {
          const wid = b[i]!
          const w = content.diagram.wires[wid]
          if (w === undefined) fail(`body node '${id}' boundary[${i}] references missing wire '${wid}' in content`)
          if (w!.scope !== content.diagram.root) {
            fail(`body node '${id}' boundary[${i}] wire '${wid}' must be scoped at content root '${content.diagram.root}', got '${w!.scope}'`)
          }
        }
        for (let i = 0; i < argCount; i++) {
          const wid = b[i]!
          const w = content.diagram.wires[wid]!
          const argSig = n.sig.args[i]!
          if (!sigEquals(w.sig, argSig)) {
            fail(`body node '${id}' boundary[${i}] wire '${wid}' sig '${sigKey(w.sig)}' does not match sig arg ${i} '${sigKey(argSig)}'`)
          }
        }
        nodes[id] = n
        break
      }
      default:
        // Exhaustiveness: a new node kind must add its own validation here.
        n satisfies never
        fail(`node '${id}' has an unrecognized kind`)
    }
  }

  // Canonicalization: from here on every term node's frees are s0, s1, …
  // and freeVar endpoints are spelled in the same canonical names.
  const { nodes: canonNodes, wires: canonWires } = canonicalizeFreePorts(nodes, wires)

  // Precomputed once per node; reused by both the wires loop and the
  // partition check below.
  const portsByNode = new Map<NodeId, Port[]>()
  for (const [id, n] of Object.entries(canonNodes)) {
    portsByNode.set(id, requiredPorts(n))
  }

  // Nested map (node -> portKey -> wire) rather than a composite string key:
  // node ids and port names are unconstrained strings, so any flat
  // serialization has an aliasing seam.
  const attached = new Map<NodeId, Map<string, WireId>>()
  for (const [wid, w] of Object.entries(canonWires)) {
    try {
      assertWellFormedSig(w.sig)
    } catch (e) {
      fail(`wire '${wid}' sig: ${e instanceof Error ? e.message : String(e)}`)
    }
    if (regions[w.scope] === undefined) fail(`wire '${wid}' has missing scope region '${w.scope}'`)
    for (const ep of w.endpoints) {
      const n = canonNodes[ep.node] ?? fail(`wire '${wid}' endpoint references missing node '${ep.node}'`)
      const key = portKey(ep.port)
      const req = portsByNode.get(ep.node)!
      if (!req.some((q) => portKey(q) === key)) {
        fail(`wire '${wid}' endpoint references non-existent port '${key}' of node '${ep.node}'`)
      }
      // Port exists (membership passed): portSig cannot throw here.
      const expected = portSig(n, ep.port)
      if (!sigEquals(w.sig, expected)) {
        fail(`wire '${wid}' sig '${sigKey(w.sig)}' does not match port '${key}' of node '${ep.node}' expecting '${sigKey(expected)}'`)
      }
      let byPort = attached.get(ep.node)
      if (byPort === undefined) {
        byPort = new Map()
        attached.set(ep.node, byPort)
      }
      const prev = byPort.get(key)
      if (prev !== undefined) {
        fail(prev === wid
          ? `port '${key}' of node '${ep.node}' appears more than once in wire '${wid}'`
          : `port '${key}' of node '${ep.node}' is attached to two wires ('${prev}' and '${wid}')`)
      }
      byPort.set(key, wid)
      if (!ancestorOrEqualRaw(regions, w.scope, n.region)) {
        fail(`wire '${wid}' scope '${w.scope}' does not enclose node '${ep.node}' (region '${n.region}')`)
      }
    }
  }

  for (const id of Object.keys(canonNodes)) {
    // portsByNode was built from the same node entries; the get cannot miss.
    for (const q of portsByNode.get(id)!) {
      if (attached.get(id)?.get(portKey(q)) === undefined) {
        fail(`port '${portKey(q)}' of node '${id}' is not attached to any wire`)
      }
    }
  }

  // Freeze is shallow: the four records are frozen, inner objects are not.
  // Compile-time readonly types are the mutation guard for typed code; rule
  // implementations (Plan 4) must construct new diagrams, never mutate.
  return Object.freeze({
    root: rootId,
    regions: Object.freeze({ ...regions }),
    nodes: Object.freeze({ ...canonNodes }),
    wires: Object.freeze({ ...canonWires }),
  })
}
