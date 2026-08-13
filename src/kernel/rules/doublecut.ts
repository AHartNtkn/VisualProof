import type { Diagram, DiagramNode, Endpoint, Region, RegionId } from '../diagram/diagram'
import { DiagramError, mkDiagram } from '../diagram/diagram'
import { derivedScope } from '../diagram/regions'
import type { SubgraphSelection } from '../diagram/subgraph/selection'
import { selectionContents } from '../diagram/subgraph/selection'
import { freshId, type IdReservation } from '../diagram/subgraph/freshId'
import { endpointDca, type PartsInProgress } from './wire-ends'
import { RuleError } from './error'

/**
 * Reparent a node into `region`, preserving its kind-specific payload.
 * Return-typed switch (no default): a new node kind forces a decision here.
 */
function reparent(n: DiagramNode, region: RegionId): DiagramNode {
  switch (n.kind) {
    case 'atom': return { kind: 'atom', region, sig: n.sig }
    case 'ref': return { kind: 'ref', region, defId: n.defId, sig: n.sig }
    case 'identity':
      return { kind: 'identity', region, sig: n.sig, arity: n.arity }
  }
}

/**
 * Wrap a selection in two fresh nested cuts. Implemented by REPARENTING —
 * every id is stable, so callers' references survive. Every quantifier stays
 * where it was: a wire whose derived scope the reparenting would move (its
 * incidences all descend into the new cuts) receives a pin at its old scope
 * — the rule's declared scope transport, sound because an even crossing
 * over the empty annulus is an equivalence. Equivalence — no polarity gate.
 */
export function applyDoubleCutIntro(d: Diagram, sel: SubgraphSelection, reservation?: IdReservation): Diagram {
  const c = selectionContents(d, sel) // validates loudly
  const taken = new Set(Object.keys(d.regions))
  const outer = freshId(taken, 'dc', reservation?.regions)
  taken.add(outer)
  const inner = freshId(taken, 'dc', reservation?.regions)
  const regions: Record<RegionId, Region> = { ...d.regions }
  regions[outer] = { kind: 'cut', parent: sel.region }
  regions[inner] = { kind: 'cut', parent: outer }
  const selectedRoots = new Set(sel.regions)
  for (const [id, r] of Object.entries(d.regions)) {
    if (r.kind !== 'sheet' && selectedRoots.has(id)) {
      regions[id] = { kind: 'cut', parent: inner }
    }
  }
  const selectedNodes = new Set(sel.nodes)
  const nodes: Record<string, DiagramNode> = { ...d.nodes }
  for (const [id, n] of Object.entries(d.nodes)) {
    if (selectedNodes.has(id)) {
      nodes[id] = reparent(n, inner)
    }
  }
  void c

  const parts: PartsInProgress = { regions, nodes, wires: { ...d.wires } }
  const takenNodes = new Set(Object.keys(nodes))
  for (const [wireId, wire] of Object.entries(d.wires)) {
    const before = derivedScope(d, wireId)
    const after = endpointDca(parts, wire.endpoints)
    if (after === before) continue
    const pin = freshId(takenNodes, 'pin', reservation?.nodes)
    takenNodes.add(pin)
    parts.nodes[pin] = { kind: 'identity', region: before, sig: wire.sig, arity: 1 }
    parts.wires[wireId] = {
      sig: wire.sig,
      endpoints: [
        ...wire.endpoints,
        { node: pin, port: { kind: 'identity', index: 0 } } satisfies Endpoint,
      ],
    }
  }
  return mkDiagram({ root: d.root, ...parts })
}

/**
 * Eliminate a double cut. The outer cut's annulus must be empty: exactly one
 * child region (a cut) and no nodes — a pin in the annulus is a node and
 * blocks, correctly: it marks a quantifier living there. Pass-through wires
 * keep their outside incidences; promoted content moves two cuts up
 * together, so every derived scope follows its nodes.
 */
export function applyDoubleCutElim(d: Diagram, outerId: RegionId): Diagram {
  const outer = d.regions[outerId]
  if (outer === undefined) throw new DiagramError(`unknown region '${outerId}'`)
  if (outer.kind !== 'cut') {
    throw new RuleError(`double-cut elimination requires a cut; '${outerId}' is a sheet`)
  }
  const children = Object.entries(d.regions).filter(([, r]) => r.kind !== 'sheet' && r.parent === outerId)
  const nodesInOuter = Object.values(d.nodes).some((n) => n.region === outerId)
  // Every non-root region is a cut (Region has no third kind), so a lone
  // child is necessarily a cut; only its presence needs checking. A wire
  // cannot be scoped in the annulus without a node there: with one child
  // subtree, no incidence set has its DCA at the annulus itself.
  const lone = children.length === 1 ? children[0]! : undefined
  if (lone === undefined || nodesInOuter) {
    throw new RuleError(`annulus '${outerId}' must contain exactly one child cut and nothing else`)
  }
  const innerId = lone[0]
  const target = outer.parent

  const regions: Record<RegionId, Region> = {}
  for (const [id, r] of Object.entries(d.regions)) {
    if (id === outerId || id === innerId) continue
    regions[id] = r.kind !== 'sheet' && r.parent === innerId
      ? { kind: 'cut', parent: target }
      : r
  }
  const nodes: Record<string, DiagramNode> = {}
  for (const [id, n] of Object.entries(d.nodes)) {
    nodes[id] = n.region === innerId ? reparent(n, target) : n
  }
  return mkDiagram({ root: d.root, regions, nodes, wires: { ...d.wires } })
}
