import type { Term } from '../term/term'
import { freePorts, renameFreePorts, assertWellFormedTerm } from '../term/term'

export type RegionId = string
export type NodeId = string
export type WireId = string

export type Region =
  | { readonly kind: 'sheet' }
  | { readonly kind: 'cut'; readonly parent: RegionId }
  | { readonly kind: 'bubble'; readonly parent: RegionId; readonly arity: number }

export type DiagramNode =
  | { readonly kind: 'term'; readonly region: RegionId; readonly term: Term }
  | { readonly kind: 'atom'; readonly region: RegionId; readonly binder: RegionId }

export type Port =
  | { readonly kind: 'output' }
  | { readonly kind: 'freeVar'; readonly name: string }
  | { readonly kind: 'arg'; readonly index: number }

export type Endpoint = { readonly node: NodeId; readonly port: Port }

/** One wire = one line of identity = one existentially scoped individual. */
export type Wire = { readonly scope: RegionId; readonly endpoints: readonly Endpoint[] }

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
  }
}

/**
 * The exact port set a node must have attached: output plus one freeVar port
 * per distinct free variable (first-occurrence order) for term nodes; arg
 * 0..arity-1 for atoms, arity read from the binder bubble.
 */
export function requiredPorts(d: { regions: Readonly<Record<RegionId, Region>> }, node: DiagramNode): Port[] {
  if (node.kind === 'term') {
    return [
      { kind: 'output' },
      ...freePorts(node.term).map((name): Port => ({ kind: 'freeVar', name })),
    ]
  }
  const binder = d.regions[node.binder]
  if (binder === undefined || binder.kind !== 'bubble') {
    throw new DiagramError(`atom binder '${node.binder}' is not a bubble`)
  }
  return Array.from({ length: binder.arity }, (_, index): Port => ({ kind: 'arg', index }))
}

/**
 * Free-port names are never semantic: every term node's free ports are
 * renamed to s0, s1, … in first-occurrence order, and the freeVar endpoints
 * of its wires are rewritten through the same per-node map — one simultaneous
 * pass, so swaps like {s0→s1, s1→s0} cannot cascade. Runs after term
 * well-formedness checks (renaming presupposes meaningful names) and before
 * port validation, so all downstream invariants hold over canonical names.
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
  for (const [id, n] of Object.entries(nodes)) {
    if (n.kind !== 'term') {
      nodesOut[id] = n
      continue
    }
    const map = new Map<string, string>()
    let identity = true
    for (const [i, name] of freePorts(n.term).entries()) {
      const to = `s${i}`
      map.set(name, to)
      if (name !== to) identity = false
    }
    renames.set(id, map)
    if (identity) {
      nodesOut[id] = n
      continue
    }
    nodesOut[id] = { kind: 'term', region: n.region, term: renameFreePorts(n.term, map) }
    nodesChanged = true
  }
  let wiresChanged = false
  const wiresOut: Record<WireId, Wire> = {}
  for (const [wid, w] of Object.entries(wires)) {
    let epsChanged = false
    const endpoints = w.endpoints.map((ep): Endpoint => {
      if (ep.port.kind !== 'freeVar') return ep
      const map = renames.get(ep.node) // undefined for atoms and missing nodes: validation rejects those endpoints
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
    wiresOut[wid] = { scope: w.scope, endpoints }
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
 * sheet; the parent graph is a tree rooted there; bubble arities are sane;
 * node regions and atom binders are valid (binder a bubble enclosing the
 * atom); wire scopes enclose every endpoint; and the wire endpoint sets
 * exactly partition the set of all required ports. Throws DiagramError with
 * a specific message on the first violation found.
 */
export function mkDiagram(parts: {
  root: RegionId
  regions: Record<RegionId, Region>
  nodes?: Record<NodeId, DiagramNode>
  wires?: Record<WireId, Wire>
}): Diagram {
  const { root: rootId } = parts
  const regions = parts.regions
  const nodes = parts.nodes ?? {}
  const wires = parts.wires ?? {}
  const fail = (msg: string): never => { throw new DiagramError(msg) }

  const root = regions[rootId] ?? fail(`root region '${rootId}' does not exist`)
  if (root.kind !== 'sheet') fail(`root region '${rootId}' must be a sheet, got '${root.kind}'`)

  for (const [id, r] of Object.entries(regions)) {
    if (r.kind === 'sheet' && id !== rootId) {
      fail(`region '${id}' is a second sheet; only the root may be a sheet`)
    }
    if (r.kind === 'bubble' && (!Number.isSafeInteger(r.arity) || r.arity < 0)) {
      fail(`bubble '${id}' arity must be a non-negative safe integer, got ${r.arity}`)
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

  for (const [id, n] of Object.entries(nodes)) {
    if (regions[n.region] === undefined) fail(`node '${id}' is in missing region '${n.region}'`)
    if (n.kind === 'term') {
      try {
        assertWellFormedTerm(n.term)
      } catch (e) {
        fail(`node '${id}' term: ${e instanceof Error ? e.message : String(e)}`)
      }
    }
    if (n.kind === 'atom') {
      const binder = regions[n.binder] ?? fail(`atom '${id}' references missing binder '${n.binder}'`)
      if (binder.kind !== 'bubble') fail(`atom '${id}' binder '${n.binder}' must be a bubble, got '${binder.kind}'`)
      if (!ancestorOrEqualRaw(regions, n.binder, n.region)) {
        fail(`atom '${id}' must lie inside its binder bubble '${n.binder}'`)
      }
    }
  }

  // Canonicalization: from here on every term node's frees are s0, s1, …
  // and freeVar endpoints are spelled in the same canonical names.
  const { nodes: canonNodes, wires: canonWires } = canonicalizeFreePorts(nodes, wires)

  // Precomputed once per node; reused by both the wires loop and the
  // partition check below.
  const portsByNode = new Map<NodeId, Port[]>()
  for (const [id, n] of Object.entries(canonNodes)) {
    portsByNode.set(id, requiredPorts({ regions }, n))
  }

  // Nested map (node -> portKey -> wire) rather than a composite string key:
  // node ids and port names are unconstrained strings, so any flat
  // serialization has an aliasing seam.
  const attached = new Map<NodeId, Map<string, WireId>>()
  for (const [wid, w] of Object.entries(canonWires)) {
    if (regions[w.scope] === undefined) fail(`wire '${wid}' has missing scope region '${w.scope}'`)
    for (const ep of w.endpoints) {
      const n = canonNodes[ep.node] ?? fail(`wire '${wid}' endpoint references missing node '${ep.node}'`)
      const key = portKey(ep.port)
      const req = portsByNode.get(ep.node)!
      if (!req.some((q) => portKey(q) === key)) {
        fail(`wire '${wid}' endpoint references non-existent port '${key}' of node '${ep.node}'`)
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
