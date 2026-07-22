import type { Diagram, DiagramNode, Region, RegionId, Wire, WireId } from '../diagram'
import { mkDiagram } from '../diagram'
import type { DiagramWithBoundary } from '../boundary'
import { mkDiagramWithBoundary } from '../boundary'
import type { SubgraphSelection } from './selection'
import { selectionContents } from './selection'
import { freshId } from './freshId'

export type Extraction = {
  readonly pattern: DiagramWithBoundary
  /** Host wires the boundary stubs came from, index-aligned with pattern.boundary. */
  readonly attachments: readonly WireId[]
}

/**
 * Non-destructive: copies the selection out as a self-contained pattern.
 * Selected items keep their host ids (the pattern is a fresh namespace); only
 * the fresh root and the boundary stub ids dodge collisions deterministically.
 * Touching wires become root-scoped stubs in sorted host-wire-id order,
 * carrying the crossing wire's signature; the original host wire ids form the
 * attachment record.
 *
 * There is no binder machinery: an atom whose head wire lies outside the
 * selection contributes that head wire as an ordinary attachment (boundary)
 * wire, exactly like an arg wire crossing the boundary. The relational sig
 * rides on the stub, so splice can gate the reattachment by sig equality.
 */
export function extractSubgraph(d: Diagram, sel: SubgraphSelection): Extraction {
  const c = selectionContents(d, sel)

  const takenRegionIds = new Set<string>(c.allRegions)
  const root = freshId(takenRegionIds, 'root')
  takenRegionIds.add(root)
  const regions: Record<RegionId, Region> = { [root]: { kind: 'sheet' } }

  const subtreeRootSet = new Set(sel.regions)
  for (const id of c.allRegions) {
    const r = d.regions[id]!
    if (r.kind === 'sheet') continue // impossible: subtree roots are non-root children
    const parent = subtreeRootSet.has(id) ? root : r.parent
    regions[id] = { kind: 'cut', parent }
  }

  // Return-typed switch (no default): a new node kind forces its rebuild here.
  const rebuildNode = (n: DiagramNode, region: RegionId): DiagramNode => {
    switch (n.kind) {
      case 'term': return { kind: 'term', region, term: n.term, freePorts: n.freePorts }
      case 'atom': return { kind: 'atom', region, sig: n.sig }
      case 'ref': return { kind: 'ref', region, defId: n.defId, sig: n.sig }
      case 'body': return { kind: 'body', region, sig: n.sig, content: n.content }
    }
  }
  const nodes: Record<string, DiagramNode> = {}
  for (const id of c.allNodes) {
    const n = d.nodes[id]!
    const region = n.region === sel.region ? root : n.region
    nodes[id] = rebuildNode(n, region)
  }

  const wires: Record<WireId, Wire> = {}
  const takenWireIds = new Set<string>(c.internalWires)
  for (const id of c.internalWires) {
    const w = d.wires[id]!
    wires[id] = {
      scope: w.scope === sel.region ? root : w.scope,
      sig: w.sig,
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
      sig: w.sig,
      endpoints: w.endpoints.filter((ep) => c.allNodes.has(ep.node)),
    }
    boundary.push(stubId)
    attachments.push(hostWireId)
  }

  const pattern = mkDiagramWithBoundary(mkDiagram({ root, regions, nodes, wires }), boundary)
  return Object.freeze({
    pattern,
    attachments: Object.freeze(attachments),
  })
}
