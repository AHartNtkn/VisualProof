import type { Diagram, DiagramNode, Region, RegionId, Wire, WireId } from '../diagram/diagram'
import { DiagramError, mkDiagram } from '../diagram/diagram'
import type { SubgraphSelection } from '../diagram/subgraph/selection'
import { selectionContents } from '../diagram/subgraph/selection'
import { freshId, type IdReservation } from '../diagram/subgraph/freshId'
import { RuleError } from './error'

/**
 * Reparent a node into `region`, preserving its kind-specific payload.
 * Return-typed switch (no default): a new node kind forces a decision here.
 */
function reparent(n: DiagramNode, region: RegionId): DiagramNode {
  switch (n.kind) {
    case 'term': return { kind: 'term', region, term: n.term, freePorts: n.freePorts }
    case 'atom': return { kind: 'atom', region, binder: n.binder }
    case 'ref': return { kind: 'ref', region, defId: n.defId, arity: n.arity }
  }
}

/**
 * Vacuous bubble introduction: wrap a selection in ONE fresh bubble of the
 * given arity. ∃R φ ≡ φ when R has no occurrences — and no atom can be bound
 * to a bubble that did not exist — so this is an equivalence at ANY polarity
 * (bubbles never flip parity, spec §2.1). Mechanics are double-cut intro's
 * reparenting with a single bubble: ids stable, selected top-level wires
 * keep their scope.
 */
export function applyVacuousBubbleIntro(d: Diagram, sel: SubgraphSelection, arity: number, reservation?: IdReservation): Diagram {
  if (!Number.isSafeInteger(arity) || arity < 0) {
    throw new DiagramError(`bubble arity must be a non-negative safe integer, got ${arity}`)
  }
  selectionContents(d, sel) // validates loudly
  const bubbleId = freshId(new Set(Object.keys(d.regions)), 'vb', reservation?.regions)
  const regions: Record<RegionId, Region> = { ...d.regions }
  regions[bubbleId] = { kind: 'bubble', parent: sel.region, arity }
  const selectedRoots = new Set(sel.regions)
  for (const [id, r] of Object.entries(d.regions)) {
    if (r.kind !== 'sheet' && selectedRoots.has(id)) {
      regions[id] = r.kind === 'cut'
        ? { kind: 'cut', parent: bubbleId }
        : { kind: 'bubble', parent: bubbleId, arity: r.arity }
    }
  }
  const selectedNodes = new Set(sel.nodes)
  const nodes: Record<string, DiagramNode> = { ...d.nodes }
  for (const [id, n] of Object.entries(d.nodes)) {
    if (selectedNodes.has(id)) {
      nodes[id] = reparent(n, bubbleId)
    }
  }
  return mkDiagram({ root: d.root, regions, nodes, wires: { ...d.wires } })
}

/**
 * Vacuous bubble elimination: dissolve a bubble binding ZERO atoms,
 * promoting its children, nodes, and wire scopes to its parent — the same
 * promotion comprehension instantiation uses, minus the splicing, gated on
 * vacuity instead of polarity (the equivalence ∃R φ ≡ φ needs R absent).
 */
export function applyVacuousBubbleElim(d: Diagram, bubbleId: RegionId): Diagram {
  const bubble = d.regions[bubbleId]
  if (bubble === undefined) throw new DiagramError(`unknown region '${bubbleId}'`)
  if (bubble.kind !== 'bubble') {
    throw new RuleError(`vacuous elimination requires a bubble; '${bubbleId}' is a ${bubble.kind}`)
  }
  const bound = Object.values(d.nodes).filter((n) => n.kind === 'atom' && n.binder === bubbleId)
  if (bound.length > 0) {
    throw new RuleError(`bubble '${bubbleId}' binds ${bound.length} atom(s); only vacuous bubbles dissolve at any polarity`)
  }
  const parent = bubble.parent
  const regions: Record<RegionId, Region> = {}
  for (const [id, r] of Object.entries(d.regions)) {
    if (id === bubbleId) continue
    regions[id] = r.kind !== 'sheet' && r.parent === bubbleId
      ? (r.kind === 'cut' ? { kind: 'cut', parent } : { kind: 'bubble', parent, arity: r.arity })
      : r
  }
  const nodes: Record<string, DiagramNode> = {}
  for (const [id, n] of Object.entries(d.nodes)) {
    nodes[id] = n.region === bubbleId ? reparent(n, parent) : n
  }
  const wires: Record<WireId, Wire> = {}
  for (const [id, w] of Object.entries(d.wires)) {
    wires[id] = w.scope === bubbleId ? { scope: parent, endpoints: w.endpoints } : w
  }
  return mkDiagram({ root: d.root, regions, nodes, wires })
}
