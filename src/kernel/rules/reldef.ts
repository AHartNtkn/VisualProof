import type { Diagram, DiagramNode, Endpoint, NodeId, Region, Wire, WireId } from '../diagram/diagram'
import { mkDiagram } from '../diagram/diagram'
import type { DiagramWithBoundary } from '../diagram/boundary'
import type { SubgraphSelection } from '../diagram/subgraph/selection'
import { extractSubgraph } from '../diagram/subgraph/extract'
import { removeSubgraph, spliceSubgraph } from '../diagram/subgraph/splice'
import { exploreForm } from '../diagram/canonical/explore'
import { freshId } from '../diagram/subgraph/freshId'
import { RuleError } from './error'
import { wireAt } from './access'

/**
 * Relation fold/unfold: a named relation reference `{kind:'ref'; defId; arity}`
 * is exactly notation for its body (a DiagramWithBoundary whose boundary wires
 * are its argument lines). Unfold replaces the reference by an inlined copy of
 * the body; fold replaces an exact copy of the body by the reference. Both are
 * definitional equivalences — the reference and the body denote the same
 * relation — so both are POLARITY-BLIND (sound at positive and negative
 * regions alike). Fold's boundary-pinned fingerprint check against the body is
 * the exactness guarantee: only an occurrence isomorphic to the body (with its
 * boundary reordered by `args`) may be replaced by the reference.
 */

/**
 * Unfold: splice the relation body onto the reference's argument wires and drop
 * the reference. The body's boundary stub i merges into arg-i's wire (the same
 * splice path insertion uses), so the body lands attached exactly where the
 * reference's argument lines were.
 */
export function applyRelUnfold(
  d: Diagram,
  node: NodeId,
  relations: ReadonlyMap<string, DiagramWithBoundary>,
): Diagram {
  const n = d.nodes[node]
  if (n === undefined) throw new RuleError(`unknown node '${node}'`)
  if (n.kind !== 'ref') throw new RuleError(`relation unfold applies to reference nodes; '${node}' has kind '${n.kind}'`)
  const body = relations.get(n.defId)
  if (body === undefined) throw new RuleError(`relation unfold: no relation named '${n.defId}'`)
  if (body.boundary.length !== n.arity) {
    throw new RuleError(
      `relation unfold: reference '${node}' has arity ${n.arity} but relation '${n.defId}' has ${body.boundary.length} boundary wires`,
    )
  }
  const args: WireId[] = []
  for (let i = 0; i < n.arity; i++) args.push(wireAt(d, node, { kind: 'arg', index: i }))
  const spliced = spliceSubgraph(d, n.region, body, args)
  return removeSubgraph(spliced, { region: n.region, regions: [], nodes: [node], wires: [] })
}

/**
 * Fold: replace an exact occurrence of the relation body by a single reference
 * node on `args`. Mirrors comprehension abstraction's occurrence check —
 * extract the selection, refuse if it binds atoms outside itself, require
 * `args` to be a distinct permutation of the occurrence's attachment wires, and
 * demand the boundary-pinned fingerprint (boundary reordered by `args`) equal
 * the relation body's. That fingerprint equality is what keeps the fold exact.
 */
export function applyRelFold(
  d: Diagram,
  sel: SubgraphSelection,
  defId: string,
  args: readonly WireId[],
  relations: ReadonlyMap<string, DiagramWithBoundary>,
): Diagram {
  const body = relations.get(defId)
  if (body === undefined) throw new RuleError(`relation fold: no relation named '${defId}'`)
  const { pattern, attachments, binderStubs } = extractSubgraph(d, sel)
  if (binderStubs.length > 0) {
    throw new RuleError(`relation fold: an occurrence with atoms bound outside it cannot be folded`)
  }
  if (args.length !== attachments.length) {
    throw new RuleError(`relation fold: the occurrence has ${attachments.length} attachment wires but ${args.length} argument positions`)
  }
  if (new Set(args).size !== args.length) {
    throw new RuleError(`relation fold: argument wires are not distinct`)
  }
  const reordered = args.map((a) => {
    const j = attachments.indexOf(a)
    if (j === -1) throw new RuleError(`relation fold: argument wire '${a}' is not one of the occurrence's attachment wires`)
    return pattern.boundary[j]!
  })
  const fp = exploreForm(pattern.diagram, reordered)
  if (fp !== exploreForm(body.diagram, body.boundary)) {
    throw new RuleError(`relation fold: the occurrence does not match relation '${defId}' (boundary-pinned canonical forms differ)`)
  }

  const cleaned = removeSubgraph(d, sel)
  const refId = freshId(new Set(Object.keys(cleaned.nodes)), 'relFold')
  const nodes: Record<NodeId, DiagramNode> = {
    ...cleaned.nodes,
    [refId]: { kind: 'ref', region: sel.region, defId, arity: args.length },
  }
  const regions: Record<string, Region> = { ...cleaned.regions }
  const wires: Record<WireId, Wire> = {}
  for (const [id, w] of Object.entries(cleaned.wires)) {
    const adds: Endpoint[] = []
    args.forEach((a, i) => {
      if (a === id) adds.push({ node: refId, port: { kind: 'arg', index: i } })
    })
    wires[id] = adds.length === 0 ? w : { scope: w.scope, endpoints: [...w.endpoints, ...adds] }
  }
  return mkDiagram({ root: cleaned.root, regions, nodes, wires })
}
