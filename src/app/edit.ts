import type { Term } from '../kernel/term/term'
import { freePorts } from '../kernel/term/term'
import type { Diagram, DiagramNode, Endpoint, NodeId, Port, Region, RegionId, Wire, WireId } from '../kernel/diagram/diagram'
import { mkDiagram, portKey } from '../kernel/diagram/diagram'
import { isAncestorOrEqual } from '../kernel/diagram/regions'
import type { SubgraphSelection } from '../kernel/diagram/subgraph/selection'
import { removeSubgraph } from '../kernel/diagram/subgraph/splice'
import { freshId } from '../kernel/diagram/subgraph/freshId'

/**
 * Construction-mode surgery. These are NOT rules: they build statements
 * before proving starts, and their only obligation is structural validity
 * (every result passes mkDiagram). The session refuses them once a proof is
 * underway.
 */

export function emptyDiagram(): Diagram {
  return mkDiagram({ root: 'r0', regions: { r0: { kind: 'sheet' } } })
}

export function addTermNode(d: Diagram, region: RegionId, term: Term): { diagram: Diagram; node: NodeId } {
  const node = freshId(new Set(Object.keys(d.nodes)), 'n')
  const nodes: Record<NodeId, DiagramNode> = { ...d.nodes, [node]: { kind: 'term', region, term } }
  const wires: Record<WireId, Wire> = { ...d.wires }
  const takenWires = new Set(Object.keys(d.wires))
  const ports: Port[] = [{ kind: 'output' }, ...freePorts(term).map((name): Port => ({ kind: 'freeVar', name }))]
  for (const port of ports) {
    const w = freshId(takenWires, 'w')
    takenWires.add(w)
    wires[w] = { scope: region, endpoints: [{ node, port }] }
  }
  return { diagram: mkDiagram({ root: d.root, regions: { ...d.regions }, nodes, wires }), node }
}

function wrap(d: Diagram, sel: SubgraphSelection, make: (parent: RegionId) => Region, base: string): { diagram: Diagram; region: RegionId } {
  const region = freshId(new Set(Object.keys(d.regions)), base)
  const regions: Record<RegionId, Region> = { ...d.regions, [region]: make(sel.region) }
  const selectedRoots = new Set(sel.regions)
  for (const [id, r] of Object.entries(d.regions)) {
    if (r.kind !== 'sheet' && selectedRoots.has(id)) {
      regions[id] = r.kind === 'cut' ? { kind: 'cut', parent: region } : { kind: 'bubble', parent: region, arity: r.arity }
    }
  }
  const selectedNodes = new Set(sel.nodes)
  const nodes: Record<NodeId, DiagramNode> = { ...d.nodes }
  for (const [id, n] of Object.entries(d.nodes)) {
    if (selectedNodes.has(id)) {
      nodes[id] = n.kind === 'term'
        ? { kind: 'term', region, term: n.term }
        : { kind: 'atom', region, binder: n.binder }
    }
  }
  return { diagram: mkDiagram({ root: d.root, regions, nodes, wires: { ...d.wires } }), region }
}

/** Wrap a selection in a SINGLE cut (construction only — proofs use double-cut intro). */
export function addCut(d: Diagram, sel: SubgraphSelection): { diagram: Diagram; region: RegionId } {
  return wrap(d, sel, (parent) => ({ kind: 'cut', parent }), 'cut')
}

export function addBubble(d: Diagram, sel: SubgraphSelection, arity: number): { diagram: Diagram; region: RegionId } {
  return wrap(d, sel, (parent) => ({ kind: 'bubble', parent, arity }), 'bub')
}

/**
 * Identify two individuals: merge the wires holding the two ports into one,
 * scoped at the deepest common scope of the originals (construction-level —
 * the rule-gated counterpart is applyWireJoin).
 */
export function joinPorts(d: Diagram, a: Endpoint, b: Endpoint): Diagram {
  if (a.node === b.node && portKey(a.port) === portKey(b.port)) {
    throw new Error('cannot join a port to the same port')
  }
  const holder = (ep: Endpoint): WireId => {
    const found = Object.entries(d.wires).find(([, w]) =>
      w.endpoints.some((x) => x.node === ep.node && portKey(x.port) === portKey(ep.port)))
    if (found === undefined) throw new Error(`no wire holds port '${portKey(ep.port)}' of node '${ep.node}'`)
    return found[0]
  }
  const wa = holder(a)
  const wb = holder(b)
  if (wa === wb) return d
  const sa = d.wires[wa]!.scope
  const sb = d.wires[wb]!.scope
  const scope = isAncestorOrEqual(d, sa, sb) ? sa
    : isAncestorOrEqual(d, sb, sa) ? sb
    : d.root
  const wires: Record<WireId, Wire> = {}
  for (const [id, w] of Object.entries(d.wires)) {
    if (id === wb) continue
    wires[id] = id === wa
      ? { scope, endpoints: [...d.wires[wa]!.endpoints, ...d.wires[wb]!.endpoints] }
      : w
  }
  return mkDiagram({ root: d.root, regions: { ...d.regions }, nodes: { ...d.nodes }, wires })
}

export function deleteSelection(d: Diagram, sel: SubgraphSelection): Diagram {
  return removeSubgraph(d, sel)
}
