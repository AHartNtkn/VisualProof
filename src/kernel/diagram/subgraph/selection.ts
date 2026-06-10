import type { Diagram, NodeId, RegionId, WireId } from '../diagram'
import { DiagramError } from '../diagram'

/**
 * A subgraph at a region: whole child subtrees, direct nodes, and explicitly
 * chosen top-level wires. Top-level wire membership is the caller's choice —
 * a wire whose endpoints all happen to be selected is still a boundary wire
 * unless listed in `wires`.
 */
export type SubgraphSelection = {
  readonly region: RegionId
  readonly regions: readonly RegionId[]
  readonly nodes: readonly NodeId[]
  readonly wires: readonly WireId[]
}

export type SelectionContents = {
  /** Every region inside the selected subtrees (the subtree roots included). */
  readonly allRegions: ReadonlySet<RegionId>
  /** Every selected node: direct ones plus all nodes inside selected subtrees. */
  readonly allNodes: ReadonlySet<NodeId>
  /** Wires wholly owned by the selection, sorted by id. */
  readonly internalWires: readonly WireId[]
  /** Wires with at least one endpoint on a selected node that are not internal, sorted by id. */
  readonly touchingWires: readonly WireId[]
}

export function mkSelection(d: Diagram, sel: SubgraphSelection): SubgraphSelection {
  if (d.regions[sel.region] === undefined) throw new DiagramError(`unknown selection region '${sel.region}'`)
  const seenR = new Set<RegionId>()
  for (const r of sel.regions) {
    const reg = d.regions[r]
    if (reg === undefined) throw new DiagramError(`unknown region '${r}'`)
    if (reg.kind === 'sheet' || reg.parent !== sel.region) {
      throw new DiagramError(`region '${r}' is not a child of selection region '${sel.region}'`)
    }
    if (seenR.has(r)) throw new DiagramError(`duplicate selected region '${r}'`)
    seenR.add(r)
  }
  const seenN = new Set<NodeId>()
  for (const n of sel.nodes) {
    const node = d.nodes[n]
    if (node === undefined) throw new DiagramError(`unknown node '${n}'`)
    if (node.region !== sel.region) {
      throw new DiagramError(`node '${n}' is not directly in selection region '${sel.region}'`)
    }
    if (seenN.has(n)) throw new DiagramError(`duplicate selected node '${n}'`)
    seenN.add(n)
  }
  // wire validation needs allNodes; compute the closure first
  const contents = computeClosure(d, seenR, seenN)
  const seenW = new Set<WireId>()
  for (const w of sel.wires) {
    const wire = d.wires[w]
    if (wire === undefined) throw new DiagramError(`unknown wire '${w}'`)
    if (wire.scope !== sel.region) {
      throw new DiagramError(`wire '${w}' is not scoped at selection region '${sel.region}'`)
    }
    if (!wire.endpoints.every((ep) => contents.allNodes.has(ep.node))) {
      throw new DiagramError(`wire '${w}' has endpoints outside the selection`)
    }
    if (seenW.has(w)) throw new DiagramError(`duplicate selected wire '${w}'`)
    seenW.add(w)
  }
  return Object.freeze({
    region: sel.region,
    regions: Object.freeze([...sel.regions]),
    nodes: Object.freeze([...sel.nodes]),
    wires: Object.freeze([...sel.wires]),
  })
}

function computeClosure(
  d: Diagram,
  subtreeRoots: ReadonlySet<RegionId>,
  directNodes: ReadonlySet<NodeId>,
): { allRegions: Set<RegionId>; allNodes: Set<NodeId> } {
  const allRegions = new Set<RegionId>(subtreeRoots)
  // expand subtrees: a region is included iff some ancestor chain hits a root
  let grew = true
  while (grew) {
    grew = false
    for (const [id, r] of Object.entries(d.regions)) {
      if (allRegions.has(id) || r.kind === 'sheet') continue
      if (allRegions.has(r.parent)) {
        allRegions.add(id)
        grew = true
      }
    }
  }
  const allNodes = new Set<NodeId>(directNodes)
  for (const [id, n] of Object.entries(d.nodes)) {
    if (allRegions.has(n.region)) allNodes.add(id)
  }
  return { allRegions, allNodes }
}

export function selectionContents(d: Diagram, sel: SubgraphSelection): SelectionContents {
  const validated = mkSelection(d, sel) // idempotent; every entry point is loud
  const { allRegions, allNodes } = computeClosure(
    d, new Set(validated.regions), new Set(validated.nodes),
  )
  const explicit = new Set(validated.wires)
  const internalWires: WireId[] = []
  const touchingWires: WireId[] = []
  for (const [id, w] of Object.entries(d.wires)) {
    if (allRegions.has(w.scope) || explicit.has(id)) {
      internalWires.push(id)
      continue
    }
    if (w.endpoints.some((ep) => allNodes.has(ep.node))) touchingWires.push(id)
  }
  internalWires.sort()
  touchingWires.sort()
  return Object.freeze({
    allRegions,
    allNodes,
    internalWires: Object.freeze(internalWires),
    touchingWires: Object.freeze(touchingWires),
  })
}
