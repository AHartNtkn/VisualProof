import type { Diagram, DiagramNode, Region, RegionId, Wire, WireId } from '../diagram'
import { DiagramError, mkDiagram } from '../diagram'
import { isAncestorOrEqual } from '../regions'
import type { DiagramWithBoundary } from '../boundary'
import { mkDiagramWithBoundary } from '../boundary'
import type { SubgraphSelection } from './selection'
import { selectionContents } from './selection'
import { freshId } from './freshId'

export type Extraction = {
  readonly pattern: DiagramWithBoundary
  /** Host wires the boundary stubs came from, index-aligned with pattern.boundary. */
  readonly attachments: readonly WireId[]
  /** Pattern stub-bubble ids standing for binders OUTSIDE the selection, outermost first. */
  readonly binderStubs: readonly RegionId[]
  /** Host bubbles the stubs stand for, index-aligned with binderStubs. */
  readonly binderAttachments: readonly RegionId[]
}

/**
 * Non-destructive: copies the selection out as a self-contained pattern.
 * Selected items keep their host ids (the pattern is a fresh namespace);
 * the fresh root, boundary stub ids, and binder stub ids dodge collisions
 * deterministically. Touching wires become root-scoped stubs in sorted
 * host-wire-id order; the original host wire ids form the attachment record.
 *
 * Atoms bound OUTSIDE the selection make the pattern OPEN: every such binder
 * necessarily encloses the anchor (it encloses each of its atoms, which lie
 * inside the anchor's subtree), so the external binders are linearly ordered
 * by ancestry. The pattern stays a VALID closed diagram by inserting a chain
 * of stub bubbles (outermost binder first) between the fresh root and the
 * content; externally bound atoms point at their stub. A binder BELOW the
 * anchor cannot occur (it would have to be selected content to contain its
 * atoms), so the old rejection survives only as an invariant check.
 */
export function extractSubgraph(d: Diagram, sel: SubgraphSelection): Extraction {
  const c = selectionContents(d, sel)
  const external = new Set<RegionId>()
  for (const id of c.allNodes) {
    const n = d.nodes[id]!
    if (n.kind === 'atom' && !c.allRegions.has(n.binder)) {
      if (!isAncestorOrEqual(d, n.binder, sel.region)) {
        throw new DiagramError(
          `atom '${id}' is bound to '${n.binder}', which neither lies in the selection nor encloses its anchor`,
        )
      }
      external.add(n.binder)
    }
  }
  // outermost first: order by position on the anchor's ancestor chain
  const chainOrder: RegionId[] = []
  {
    let cur: RegionId = sel.region
    for (;;) {
      if (external.has(cur)) chainOrder.push(cur)
      const r = d.regions[cur]!
      if (r.kind === 'sheet') break
      cur = r.parent
    }
    chainOrder.reverse()
  }

  const takenRegionIds = new Set<string>(c.allRegions)
  const root = freshId(takenRegionIds, 'root')
  takenRegionIds.add(root)
  const stubOf = new Map<RegionId, RegionId>()
  const binderStubs: RegionId[] = []
  let layerParent: RegionId = root
  const regions: Record<RegionId, Region> = { [root]: { kind: 'sheet' } }
  for (const hostBinder of chainOrder) {
    const stub = freshId(takenRegionIds, 'binder')
    takenRegionIds.add(stub)
    const hb = d.regions[hostBinder]!
    if (hb.kind !== 'bubble') {
      throw new DiagramError(`atom binder '${hostBinder}' is not a bubble`) // unreachable on validated hosts
    }
    regions[stub] = { kind: 'bubble', parent: layerParent, arity: hb.arity }
    stubOf.set(hostBinder, stub)
    binderStubs.push(stub)
    layerParent = stub
  }
  const contentParent = layerParent

  const subtreeRootSet = new Set(sel.regions)
  for (const id of c.allRegions) {
    const r = d.regions[id]!
    if (r.kind === 'sheet') continue // impossible: subtree roots are non-root children
    const parent = subtreeRootSet.has(id) ? contentParent : r.parent
    regions[id] = r.kind === 'cut'
      ? { kind: 'cut', parent }
      : { kind: 'bubble', parent, arity: r.arity }
  }

  // Return-typed switch (no default): a new node kind forces its rebuild here.
  const rebuildNode = (n: DiagramNode, region: RegionId): DiagramNode => {
    switch (n.kind) {
      case 'term': return { kind: 'term', region, term: n.term, freePorts: n.freePorts }
      case 'atom': return { kind: 'atom', region, binder: stubOf.get(n.binder) ?? n.binder }
      case 'ref': return { kind: 'ref', region, defId: n.defId, arity: n.arity }
    }
  }
  const nodes: Record<string, DiagramNode> = {}
  for (const id of c.allNodes) {
    const n = d.nodes[id]!
    const region = n.region === sel.region ? contentParent : n.region
    nodes[id] = rebuildNode(n, region)
  }

  const wires: Record<WireId, Wire> = {}
  const takenWireIds = new Set<string>(c.internalWires)
  for (const id of c.internalWires) {
    const w = d.wires[id]!
    wires[id] = {
      scope: w.scope === sel.region ? contentParent : w.scope,
      endpoints: w.endpoints,
    }
  }

  const boundary: WireId[] = []
  const attachments: WireId[] = []
  for (const hostWireId of c.touchingWires) {
    const w = d.wires[hostWireId]!
    const stubId = freshId(takenWireIds, `b${boundary.length}`)
    takenWireIds.add(stubId)
    wires[stubId] = {
      scope: root,
      endpoints: w.endpoints.filter((ep) => c.allNodes.has(ep.node)),
    }
    boundary.push(stubId)
    attachments.push(hostWireId)
  }

  const pattern = mkDiagramWithBoundary(mkDiagram({ root, regions, nodes, wires }), boundary)
  return Object.freeze({
    pattern,
    attachments: Object.freeze(attachments),
    binderStubs: Object.freeze(binderStubs),
    binderAttachments: Object.freeze(chainOrder),
  })
}
