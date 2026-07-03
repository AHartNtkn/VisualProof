import type { Diagram, DiagramNode, Endpoint, NodeId, Region, RegionId, Wire, WireId } from '../diagram/diagram'
import { DiagramError, mkDiagram } from '../diagram/diagram'
import { polarity, isAncestorOrEqual } from '../diagram/regions'
import type { DiagramWithBoundary } from '../diagram/boundary'
import type { SubgraphSelection } from '../diagram/subgraph/selection'
import { selectionContents } from '../diagram/subgraph/selection'
import { extractSubgraph } from '../diagram/subgraph/extract'
import { spliceSubgraph } from '../diagram/subgraph/splice'
import { exploreForm } from '../diagram/canonical/explore'
import { freshId } from '../diagram/subgraph/freshId'
import { RuleError } from './error'
import { wireAt } from './access'

/**
 * Reparent a node into `region`, preserving its kind-specific payload.
 * Return-typed switch (no default): a new node kind forces a decision here.
 */
function reparent(n: DiagramNode, region: RegionId): DiagramNode {
  switch (n.kind) {
    case 'term': return { kind: 'term', region, term: n.term }
    case 'atom': return { kind: 'atom', region, binder: n.binder }
    case 'ref': return { kind: 'ref', region, defId: n.defId, arity: n.arity }
  }
}

/** Remove one node, trimming its endpoints off their wires. */
function dropNode(d: Diagram, nodeId: NodeId): Diagram {
  const nodes: Record<NodeId, DiagramNode> = {}
  for (const [id, n] of Object.entries(d.nodes)) {
    if (id !== nodeId) nodes[id] = n
  }
  const wires: Record<WireId, Wire> = {}
  for (const [id, w] of Object.entries(d.wires)) {
    wires[id] = { scope: w.scope, endpoints: w.endpoints.filter((ep) => ep.node !== nodeId) }
  }
  return mkDiagram({ root: d.root, regions: { ...d.regions }, nodes, wires })
}

/**
 * Rule 8, instantiation direction (spec §3.1): at a NEGATIVE position,
 * ∃R.φ(R) may be replaced by φ(G) — splice a copy of the comprehension G at
 * every atom the bubble binds (boundary wire i onto the atom's arg-i wire),
 * then dissolve the bubble, promoting its contents to its parent. The gate
 * tests the bubble's own polarity, which equals its parent's: bubbles never
 * flip parity (spec §2.1).
 *
 * Comprehension with parameters (textbook SO comprehension): the comp's
 * boundary is `arity` argument stubs FOLLOWED BY parameter wires, positional
 * and exact. Each copy's trailing boundary stubs splice onto the SAME host
 * `attachments` wires — sharing across instances is what makes them
 * parameters (G is one fixed relation R := λx⃗. ψ(x⃗, b⃗) over host lines b⃗).
 * Per-copy enclosure of each parameter wire over the copy's landing region is
 * the splice's own attachment validation; this rule enforces existence and
 * the count split itself.
 */
export function applyComprehensionInstantiate(
  d: Diagram,
  bubbleId: RegionId,
  comp: DiagramWithBoundary,
  attachments: readonly WireId[],
  binders: ReadonlyMap<RegionId, RegionId> = new Map(),
): Diagram {
  const bubble = d.regions[bubbleId]
  if (bubble === undefined) throw new DiagramError(`unknown region '${bubbleId}'`)
  if (bubble.kind !== 'bubble') {
    throw new RuleError(`comprehension instantiation requires a bubble; '${bubbleId}' is a ${bubble.kind}`)
  }
  if (polarity(d, bubbleId) !== 'negative') {
    throw new RuleError(`comprehension instantiation requires a negative bubble; '${bubbleId}' is positive`)
  }
  if (comp.boundary.length !== bubble.arity + attachments.length) {
    throw new RuleError(
      `arity mismatch: bubble '${bubbleId}' binds a relation of arity ${bubble.arity} and ${attachments.length} parameter attachments were given, but the comprehension has ${comp.boundary.length} boundary wires`,
    )
  }
  for (const a of attachments) {
    if (d.wires[a] === undefined) {
      throw new RuleError(`parameter attachment wire '${a}' does not exist`)
    }
  }

  // Open comprehensions mention relation variables quantified OUTSIDE the
  // bubble being eliminated — a binder at or below it would let the
  // comprehension's denotation vary under that very quantifier, which the
  // instantiation argument (φ(G) ⟹ ∃R.φ(R) for FIXED G) cannot license.
  for (const hb of binders.values()) {
    if (hb === bubbleId || !isAncestorOrEqual(d, hb, bubbleId)) {
      throw new RuleError(
        `open comprehension binder '${hb}' must properly enclose the instantiated bubble '${bubbleId}'`,
      )
    }
  }
  const atoms = Object.entries(d.nodes).filter(
    (entry): entry is [NodeId, Extract<DiagramNode, { kind: 'atom' }>] =>
      entry[1].kind === 'atom' && entry[1].binder === bubbleId,
  )
  let cur = d
  for (const [atomId, atom] of atoms) {
    const args: WireId[] = []
    for (let i = 0; i < bubble.arity; i++) {
      args.push(wireAt(cur, atomId, { kind: 'arg', index: i }))
    }
    cur = spliceSubgraph(cur, atom.region, comp, [...args, ...attachments], binders)
    cur = dropNode(cur, atomId)
  }
  // dissolve the bubble: promote child regions, nodes, and wire scopes
  const parent = bubble.parent
  const regions: Record<RegionId, Region> = {}
  for (const [id, r] of Object.entries(cur.regions)) {
    if (id === bubbleId) continue
    regions[id] = r.kind !== 'sheet' && r.parent === bubbleId
      ? (r.kind === 'cut' ? { kind: 'cut', parent } : { kind: 'bubble', parent, arity: r.arity })
      : r
  }
  const nodes: Record<NodeId, DiagramNode> = {}
  for (const [id, n] of Object.entries(cur.nodes)) {
    nodes[id] = n.region === bubbleId ? reparent(n, parent) : n
  }
  const wires: Record<WireId, Wire> = {}
  for (const [id, w] of Object.entries(cur.wires)) {
    wires[id] = w.scope === bubbleId ? { scope: parent, endpoints: w.endpoints } : w
  }
  return mkDiagram({ root: cur.root, regions, nodes, wires })
}

export type AbstractionOccurrence = {
  readonly sel: SubgraphSelection
  /** Host wire serving as relation argument i — a permutation of the occurrence's attachment wires. */
  readonly args: readonly WireId[]
}

/**
 * Rule 8, abstraction direction: at a POSITIVE region, φ(G) may be replaced
 * by ∃R.φ(R) — wrap the selected content in a fresh bubble (double-cut
 * intro's reparenting, one bubble instead of two cuts; selected top-level
 * wires keep their scope: ∃x ∃R φ ⟺ ∃R ∃x φ) and replace each chosen
 * occurrence of G by an atom whose arg-i port lands on the occurrence's
 * argument-i wire. Consistency is exact: each occurrence's extracted pattern,
 * with its boundary reordered by args, must have the same boundary-pinned
 * fingerprint as the comprehension (equal pinned fingerprints iff isomorphic
 * respecting boundary order).
 */
export function applyComprehensionAbstract(
  d: Diagram,
  wrap: SubgraphSelection,
  comp: DiagramWithBoundary,
  occurrences: readonly AbstractionOccurrence[],
): Diagram {
  const wc = selectionContents(d, wrap) // validates the wrap selection loudly
  if (polarity(d, wrap.region) !== 'positive') {
    throw new RuleError(`comprehension abstraction requires a positive region; '${wrap.region}' is negative`)
  }
  const compFp = exploreForm(comp.diagram, comp.boundary)
  const seenNodes = new Set<NodeId>()
  const seenRegions = new Set<RegionId>()
  const seenWires = new Set<WireId>()
  occurrences.forEach((occ, k) => {
    const c = selectionContents(d, occ.sel)
    if (!(occ.sel.region === wrap.region || wc.allRegions.has(occ.sel.region))) {
      throw new RuleError(`occurrence ${k} is anchored at '${occ.sel.region}', outside the wrapped content`)
    }
    for (const n of c.allNodes) {
      if (!wc.allNodes.has(n)) throw new RuleError(`occurrence ${k} node '${n}' is outside the wrapped content`)
      if (seenNodes.has(n)) throw new RuleError(`occurrences overlap at node '${n}'`)
      seenNodes.add(n)
    }
    for (const r of c.allRegions) {
      if (!wc.allRegions.has(r)) throw new RuleError(`occurrence ${k} region '${r}' is outside the wrapped content`)
      if (seenRegions.has(r)) throw new RuleError(`occurrences overlap at region '${r}'`)
      seenRegions.add(r)
    }
    for (const w of c.internalWires) {
      if (seenWires.has(w)) throw new RuleError(`occurrences overlap at wire '${w}'`)
      seenWires.add(w)
    }
    const { pattern, attachments, binderStubs } = extractSubgraph(d, occ.sel)
    if (binderStubs.length > 0) {
      throw new RuleError(`occurrence ${k}: subgraphs with atoms bound outside the occurrence cannot be abstracted`)
    }
    if (occ.args.length !== attachments.length) {
      throw new RuleError(`occurrence ${k} has ${attachments.length} attachment wires but ${occ.args.length} argument positions`)
    }
    if (new Set(occ.args).size !== occ.args.length) {
      throw new RuleError(`occurrence ${k} argument wires are not distinct`)
    }
    const reordered = occ.args.map((a) => {
      const j = attachments.indexOf(a)
      if (j === -1) throw new RuleError(`occurrence ${k} argument wire '${a}' is not one of its attachment wires`)
      return pattern.boundary[j]!
    })
    const fp = exploreForm(pattern.diagram, reordered)
    if (fp !== compFp) {
      throw new RuleError(`occurrence ${k} does not match the comprehension (boundary-pinned canonical forms differ)`)
    }
  })
  occurrences.forEach((occ, k) => {
    if (occ.sel.region !== wrap.region && seenRegions.has(occ.sel.region)) {
      throw new RuleError(`occurrence ${k} is anchored inside another occurrence's content ('${occ.sel.region}')`)
    }
  })

  const bubbleId = freshId(new Set(Object.keys(d.regions)), 'cm')
  const selectedRoots = new Set(wrap.regions)
  const regions: Record<RegionId, Region> = {
    [bubbleId]: { kind: 'bubble', parent: wrap.region, arity: comp.boundary.length },
  }
  for (const [id, r] of Object.entries(d.regions)) {
    if (seenRegions.has(id)) continue
    if (r.kind !== 'sheet' && selectedRoots.has(id)) {
      regions[id] = r.kind === 'cut'
        ? { kind: 'cut', parent: bubbleId }
        : { kind: 'bubble', parent: bubbleId, arity: r.arity }
    } else {
      regions[id] = r
    }
  }
  const selectedNodes = new Set(wrap.nodes)
  const nodes: Record<NodeId, DiagramNode> = {}
  for (const [id, n] of Object.entries(d.nodes)) {
    if (seenNodes.has(id)) continue
    nodes[id] = selectedNodes.has(id) ? reparent(n, bubbleId) : n
  }
  const takenNodeIds = new Set(Object.keys(d.nodes))
  const atomIds = occurrences.map(() => {
    const id = freshId(takenNodeIds, 'cmAtom')
    takenNodeIds.add(id)
    return id
  })
  occurrences.forEach((occ, k) => {
    const anchor = occ.sel.region === wrap.region ? bubbleId : occ.sel.region
    nodes[atomIds[k]!] = { kind: 'atom', region: anchor, binder: bubbleId }
  })
  const wires: Record<WireId, Wire> = {}
  for (const [id, w] of Object.entries(d.wires)) {
    if (seenWires.has(id)) continue
    const adds: Endpoint[] = []
    occurrences.forEach((occ, k) => {
      occ.args.forEach((a, i) => {
        if (a === id) adds.push({ node: atomIds[k]!, port: { kind: 'arg', index: i } })
      })
    })
    wires[id] = { scope: w.scope, endpoints: [...w.endpoints.filter((ep) => !seenNodes.has(ep.node)), ...adds] }
  }
  return mkDiagram({ root: d.root, regions, nodes, wires })
}
