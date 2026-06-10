import type { Diagram, DiagramNode, Region, RegionId, Wire, WireId } from '../diagram/diagram'
import { DiagramError, mkDiagram } from '../diagram/diagram'
import type { SubgraphSelection } from '../diagram/subgraph/selection'
import { selectionContents } from '../diagram/subgraph/selection'
import { freshId } from '../diagram/subgraph/freshId'
import { RuleError } from './error'

/**
 * Rule 4a (spec §3.1): wrap a selection in two fresh nested cuts. Implemented
 * by REPARENTING — every id is stable, so callers' references survive.
 * Explicitly selected top-level wires keep their scope: they pass through the
 * empty annulus (∃x · ¬¬φ(x) ≡ ∃x · φ(x)). Equivalence — no polarity gate.
 */
export function applyDoubleCutIntro(d: Diagram, sel: SubgraphSelection): Diagram {
  const c = selectionContents(d, sel) // validates loudly
  const taken = new Set(Object.keys(d.regions))
  const outer = freshId(taken, 'dc')
  taken.add(outer)
  const inner = freshId(taken, 'dc')
  const regions: Record<RegionId, Region> = { ...d.regions }
  regions[outer] = { kind: 'cut', parent: sel.region }
  regions[inner] = { kind: 'cut', parent: outer }
  const selectedRoots = new Set(sel.regions)
  for (const [id, r] of Object.entries(d.regions)) {
    if (r.kind !== 'sheet' && selectedRoots.has(id)) {
      regions[id] = r.kind === 'cut'
        ? { kind: 'cut', parent: inner }
        : { kind: 'bubble', parent: inner, arity: r.arity }
    }
  }
  const selectedNodes = new Set(sel.nodes)
  const nodes: Record<string, DiagramNode> = { ...d.nodes }
  for (const [id, n] of Object.entries(d.nodes)) {
    if (selectedNodes.has(id)) {
      nodes[id] = n.kind === 'term'
        ? { kind: 'term', region: inner, term: n.term }
        : { kind: 'atom', region: inner, binder: n.binder }
    }
  }
  void c
  return mkDiagram({ root: d.root, regions, nodes, wires: { ...d.wires } })
}

/**
 * Rule 4b: eliminate a double cut. The outer cut's annulus must be empty:
 * exactly one child region (a cut), no nodes, no wires SCOPED there
 * (pass-through wires are scoped above and unaffected). The inner cut's
 * contents are promoted to the outer cut's parent.
 */
export function applyDoubleCutElim(d: Diagram, outerId: RegionId): Diagram {
  const outer = d.regions[outerId]
  if (outer === undefined) throw new DiagramError(`unknown region '${outerId}'`)
  if (outer.kind !== 'cut') {
    throw new RuleError(`double-cut elimination requires a cut; '${outerId}' is a ${outer.kind === 'sheet' ? 'sheet' : 'bubble'}`)
  }
  const children = Object.entries(d.regions).filter(([, r]) => r.kind !== 'sheet' && r.parent === outerId)
  const nodesInOuter = Object.values(d.nodes).some((n) => n.region === outerId)
  const wiresInOuter = Object.values(d.wires).some((w) => w.scope === outerId)
  const lone = children.length === 1 ? children[0]! : undefined
  if (lone === undefined || lone[1].kind !== 'cut' || nodesInOuter || wiresInOuter) {
    throw new RuleError(`annulus '${outerId}' must contain exactly one child cut and nothing else`)
  }
  const innerId = lone[0]
  const target = outer.parent

  const regions: Record<RegionId, Region> = {}
  for (const [id, r] of Object.entries(d.regions)) {
    if (id === outerId || id === innerId) continue
    if (r.kind !== 'sheet' && r.parent === innerId) {
      regions[id] = r.kind === 'cut'
        ? { kind: 'cut', parent: target }
        : { kind: 'bubble', parent: target, arity: r.arity }
    } else {
      regions[id] = r
    }
  }
  const nodes: Record<string, DiagramNode> = {}
  for (const [id, n] of Object.entries(d.nodes)) {
    nodes[id] = n.region === innerId
      ? (n.kind === 'term'
        ? { kind: 'term', region: target, term: n.term }
        : { kind: 'atom', region: target, binder: n.binder })
      : n
  }
  const wires: Record<WireId, Wire> = {}
  for (const [id, w] of Object.entries(d.wires)) {
    wires[id] = w.scope === innerId ? { scope: target, endpoints: w.endpoints } : w
  }
  return mkDiagram({ root: d.root, regions, nodes, wires })
}
