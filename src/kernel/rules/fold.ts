import type { Diagram, DiagramNode, Endpoint, NodeId, Region, Wire, WireId } from '../diagram/diagram'
import { DiagramError, mkDiagram } from '../diagram/diagram'
import type { DiagramWithBoundary } from '../diagram/boundary'
import { mkDiagramWithBoundary } from '../diagram/boundary'
import type { RelSig } from '../diagram/sig'
import { sigEquals, sigKey } from '../diagram/sig'
import type { SubgraphSelection } from '../diagram/subgraph/selection'
import { extractSubgraph } from '../diagram/subgraph/extract'
import { removeSubgraph, spliceSubgraphMapped } from '../diagram/subgraph/splice'
import { exploreForm } from '../diagram/canonical/explore'
import { freshId, type IdReservation } from '../diagram/subgraph/freshId'
import { RuleError } from './error'
import { wireAt } from './access'

/**
 * Fold / unfold — the definitional rewriting of a relation by its body.
 *
 * A relation may be witnessed two ways, and this one rule covers both:
 *  - a named reference `{kind:'ref'; defId; sig}` denotes a closed definition
 *    whose body is supplied by a `resolve(defId)` callback (no parameters —
 *    named defs are closed);
 *  - a bare atom `{kind:'atom'; sig}` on a relational wire that carries a
 *    `{kind:'body'}` node denotes that wire's witness `λx⃗. ψ(x⃗, b⃗)`, whose
 *    body content is the body node's `content` and whose parameters `b⃗` are the
 *    host lines feeding the body node's freeVar ports.
 *
 * Unfold replaces the reference/atom by an inlined copy of the body content;
 * fold replaces an exact copy of the body content by a single reference/atom.
 * Both are equals-for-equals: the reference/atom and the body content denote
 * the same relation, so both directions are sound at POSITIVE and NEGATIVE
 * regions alike (POLARITY-FREE). Fold's exactness is the boundary-pinned
 * canonical-form check: only an occurrence isomorphic to the body content (its
 * boundary reordered by the fold's argument wires, and diagonalized where those
 * wires repeat) may be replaced.
 */

/** The body node whose output endpoint lies on `wireId`, or undefined for a bare wire. */
function bodyOnWire(d: Diagram, wireId: WireId): { id: NodeId; node: Extract<DiagramNode, { kind: 'body' }> } | undefined {
  const w = d.wires[wireId]
  if (w === undefined) throw new DiagramError(`unknown wire '${wireId}'`)
  for (const ep of w.endpoints) {
    if (ep.port.kind === 'output') {
      const n = d.nodes[ep.node]
      if (n !== undefined && n.kind === 'body') return { id: ep.node, node: n }
    }
  }
  return undefined
}

/** Host lines feeding the body node's parameter freeVar ports p0..p(count-1), in order. */
function bodyParamWires(d: Diagram, bodyId: NodeId, count: number): WireId[] {
  const out: WireId[] = []
  for (let j = 0; j < count; j++) out.push(wireAt(d, bodyId, { kind: 'freeVar', name: `p${j}` }))
  return out
}

/** Validate a closed body (no params) against a ref's sig: boundary length and per-stub sorts. */
function assertRefBody(defId: string, sig: RelSig, content: DiagramWithBoundary): void {
  const argCount = sig.args.length
  if (content.boundary.length !== argCount) {
    throw new RuleError(
      `unfold: reference of arity ${argCount} but relation '${defId}' has ${content.boundary.length} boundary wires`,
    )
  }
  for (let i = 0; i < argCount; i++) {
    const stub = content.diagram.wires[content.boundary[i]!]!
    if (!sigEquals(stub.sig, sig.args[i]!)) {
      throw new RuleError(
        `unfold: relation '${defId}' boundary ${i} sort '${sigKey(stub.sig)}' does not match reference arg sort '${sigKey(sig.args[i]!)}'`,
      )
    }
  }
}

/**
 * Unfold: splice a fresh copy of the body content at the atom/ref region — its
 * arg stubs onto the node's argument wires, its parameter stubs (atom flavor
 * only) onto the body node's parameter lines — then drop the atom/ref. The body
 * node of an atom flavor is left in place: the witness is the wire's definition,
 * not consumed by a single unfold.
 */
export function applyUnfold(
  d: Diagram,
  node: NodeId,
  resolve: (defId: string) => DiagramWithBoundary | undefined,
  reservation?: IdReservation,
): Diagram {
  const n = d.nodes[node]
  if (n === undefined) throw new DiagramError(`unknown node '${node}'`)

  let content: DiagramWithBoundary
  const attachments: WireId[] = []

  if (n.kind === 'ref') {
    const body = resolve(n.defId)
    if (body === undefined) throw new RuleError(`unfold: no relation named '${n.defId}'`)
    assertRefBody(n.defId, n.sig, body)
    content = body
    for (let i = 0; i < n.sig.args.length; i++) attachments.push(wireAt(d, node, { kind: 'arg', index: i }))
  } else if (n.kind === 'atom') {
    const headWire = wireAt(d, node, { kind: 'head' })
    const b = bodyOnWire(d, headWire)
    if (b === undefined) throw new RuleError(`atom '${node}' head wire carries no body to unfold`)
    content = b.node.content
    const argCount = n.sig.args.length
    const paramCount = content.boundary.length - argCount
    for (let i = 0; i < argCount; i++) attachments.push(wireAt(d, node, { kind: 'arg', index: i }))
    for (const p of bodyParamWires(d, b.id, paramCount)) attachments.push(p)
  } else {
    throw new RuleError(`fold/unfold applies to atom or ref nodes; '${node}' has kind '${n.kind}'`)
  }

  const spliced = spliceSubgraphMapped(d, n.region, content, attachments, { reserved: reservation }).diagram
  return removeSubgraph(spliced, { region: n.region, regions: [], nodes: [node], wires: [] })
}

/**
 * A copy of `content` whose boundary wires are merged per `aliasPattern`:
 * positions carrying the same label OR already exposing the same intrinsic wire
 * share one root-scoped wire (endpoint sets unioned once). This is the
 * diagonalized relation the occurrence must meet when a fold's argument wires
 * repeat. The identity pattern merges nothing. Pure: `content` is unchanged.
 */
function diagonalize(content: DiagramWithBoundary, aliasPattern: readonly number[]): DiagramWithBoundary {
  if (aliasPattern.length !== content.boundary.length) {
    throw new DiagramError(
      `alias pattern length ${aliasPattern.length} does not match relation arity ${content.boundary.length}`,
    )
  }
  const parent = aliasPattern.map((_, i) => i)
  const find = (i: number): number => parent[i] === i ? i : (parent[i] = find(parent[i]!))
  const unite = (a: number, b: number): void => {
    const ra = find(a), rb = find(b)
    if (ra !== rb) parent[rb] = ra
  }
  const firstLabel = new Map<number, number>()
  const firstWire = new Map<WireId, number>()
  for (let i = 0; i < aliasPattern.length; i++) {
    const label = aliasPattern[i]!
    const wire = content.boundary[i]!
    const lp = firstLabel.get(label)
    if (lp === undefined) firstLabel.set(label, i); else unite(lp, i)
    const wp = firstWire.get(wire)
    if (wp === undefined) firstWire.set(wire, i); else unite(wp, i)
  }
  const classes: number[][] = []
  const classIndex = new Map<number, number>()
  for (let i = 0; i < aliasPattern.length; i++) {
    const root = find(i)
    let k = classIndex.get(root)
    if (k === undefined) { k = classes.length; classIndex.set(root, k); classes.push([]) }
    classes[k]!.push(i)
  }
  const d = content.diagram
  const endpointsOf: Record<WireId, Endpoint[]> = {}
  for (const [id, w] of Object.entries(d.wires)) endpointsOf[id] = [...w.endpoints]
  const newBoundary: WireId[] = []
  for (const positions of classes) {
    const repWire = content.boundary[positions[0]!]!
    newBoundary.push(repWire)
    const members = [...new Set(positions.map((i) => content.boundary[i]!))]
    for (const memberWire of members) {
      if (memberWire === repWire) continue
      endpointsOf[repWire]!.push(...endpointsOf[memberWire]!)
      delete endpointsOf[memberWire]
    }
  }
  const wires: Record<WireId, Wire> = {}
  for (const [id, eps] of Object.entries(endpointsOf)) {
    wires[id] = { scope: d.wires[id]!.scope, sig: d.wires[id]!.sig, endpoints: eps }
  }
  const diagram = mkDiagram({ root: d.root, regions: { ...d.regions }, nodes: { ...d.nodes }, wires })
  return mkDiagramWithBoundary(diagram, newBoundary)
}

export type FoldTarget =
  | { readonly wireId: WireId }
  | { readonly defId: string; readonly sig: RelSig; readonly resolve: (defId: string) => DiagramWithBoundary | undefined }

/**
 * Fold: replace an exact occurrence of a relation body by a single atom (on a
 * bodied target wire) or ref (on a named definition). `args` gives one host
 * wire per argument POSITION of the body (repeats express a diagonal); the body
 * parameters come from the target itself (the body node's parameter lines for
 * the atom flavor; none for the closed ref flavor). The occurrence's extracted
 * pattern, its boundary reordered by (args ++ parameters) and the body content
 * diagonalized by the same aliasing, must have equal boundary-pinned canonical
 * forms — the exactness guarantee. An occurrence attachment referencing a line
 * OUTSIDE it (e.g. an inner atom whose head wire is an outer relation parameter)
 * is legal: it must correspond to a parameter position of the body content, or
 * the fingerprint check refuses the fold.
 */
export function applyFold(
  d: Diagram,
  occurrence: SubgraphSelection,
  args: readonly WireId[],
  target: FoldTarget,
  reservation?: IdReservation,
): Diagram {
  const { pattern, attachments } = extractSubgraph(d, occurrence)

  let content: DiagramWithBoundary
  let fullArgs: WireId[]
  let insert:
    | { kind: 'atom'; wireId: WireId; sig: RelSig }
    | { kind: 'ref'; defId: string; sig: RelSig }

  if ('wireId' in target) {
    const w = d.wires[target.wireId]
    if (w === undefined) throw new DiagramError(`unknown wire '${target.wireId}'`)
    const b = bodyOnWire(d, target.wireId)
    if (b === undefined) throw new RuleError(`fold: target wire '${target.wireId}' carries no body to fold against`)
    content = b.node.content
    const sig = b.node.sig
    const argCount = sig.args.length
    if (args.length !== argCount) {
      throw new RuleError(`fold: target relation has arity ${argCount} but ${args.length} argument wires were given`)
    }
    const paramCount = content.boundary.length - argCount
    fullArgs = [...args, ...bodyParamWires(d, b.id, paramCount)]
    insert = { kind: 'atom', wireId: target.wireId, sig }
  } else {
    const body = target.resolve(target.defId)
    if (body === undefined) throw new RuleError(`fold: no relation named '${target.defId}'`)
    assertRefBody(target.defId, target.sig, body)
    content = body
    if (args.length !== target.sig.args.length) {
      throw new RuleError(`fold: relation '${target.defId}' has arity ${target.sig.args.length} but ${args.length} argument wires were given`)
    }
    fullArgs = [...args]
    insert = { kind: 'ref', defId: target.defId, sig: target.sig }
  }

  if (fullArgs.length !== content.boundary.length) {
    throw new RuleError(
      `fold: ${fullArgs.length} argument/parameter positions but the body has ${content.boundary.length} boundary wires`,
    )
  }

  // Group positions sharing a wire, labelling classes in first-appearance order.
  const classOf = new Map<WireId, number>()
  const aliasPattern = fullArgs.map((a) => {
    if (!classOf.has(a)) classOf.set(a, classOf.size)
    return classOf.get(a)!
  })
  const distinctArgs = [...classOf.keys()]
  for (const at of attachments) {
    if (!classOf.has(at)) {
      throw new RuleError(`fold: attachment wire '${at}' is not used by any argument position`)
    }
  }
  const reordered = distinctArgs.map((a) => {
    const j = attachments.indexOf(a)
    if (j === -1) throw new RuleError(`fold: argument wire '${a}' is not one of the occurrence's attachment wires`)
    return pattern.boundary[j]!
  })
  const diag = diagonalize(content, aliasPattern)
  if (exploreForm(pattern.diagram, reordered) !== exploreForm(diag.diagram, diag.boundary)) {
    throw new RuleError(`fold: the occurrence does not match the body (boundary-pinned canonical forms differ)`)
  }

  const cleaned = removeSubgraph(d, occurrence)
  // Mint against the FULL pre-removal id set (the applyTheorem discipline):
  // minting after removal can resurrect a just-deleted node id.
  const newId = freshId(new Set(Object.keys(d.nodes)), 'fold', reservation?.nodes)
  const newNode: DiagramNode = insert.kind === 'atom'
    ? { kind: 'atom', region: occurrence.region, sig: insert.sig }
    : { kind: 'ref', region: occurrence.region, defId: insert.defId, sig: insert.sig }
  const nodes: Record<NodeId, DiagramNode> = { ...cleaned.nodes, [newId]: newNode }
  const regions: Record<string, Region> = { ...cleaned.regions }
  const headWire = insert.kind === 'atom' ? insert.wireId : undefined
  const wires: Record<WireId, Wire> = {}
  for (const [id, w] of Object.entries(cleaned.wires)) {
    const adds: Endpoint[] = []
    if (id === headWire) adds.push({ node: newId, port: { kind: 'head' } })
    args.forEach((a, i) => {
      if (a === id) adds.push({ node: newId, port: { kind: 'arg', index: i } })
    })
    wires[id] = adds.length === 0 ? w : { scope: w.scope, sig: w.sig, endpoints: [...w.endpoints, ...adds] }
  }
  return mkDiagram({ root: cleaned.root, regions, nodes, wires })
}
