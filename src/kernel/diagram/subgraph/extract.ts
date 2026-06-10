import type { Diagram, DiagramNode, Region, RegionId, Wire, WireId } from '../diagram'
import { DiagramError, mkDiagram } from '../diagram'
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
 * Selected items keep their host ids (the pattern is a fresh namespace);
 * the fresh root and boundary stub ids dodge collisions deterministically.
 * Boundary stubs are root-scoped by construction — the invariant splice
 * relies on. Touching wires become stubs in sorted host-wire-id order,
 * keeping only the selected endpoints; the original host wire ids form the
 * attachment record.
 */
export function extractSubgraph(d: Diagram, sel: SubgraphSelection): Extraction {
  const c = selectionContents(d, sel)
  // Atoms can only be extracted with their binder: a binder outside the
  // selected content (including the anchor region itself — the pattern root
  // is a sheet and cannot bind) makes the pattern unconstructible.
  for (const id of c.allNodes) {
    const n = d.nodes[id]!
    if (n.kind === 'atom' && !c.allRegions.has(n.binder)) {
      throw new DiagramError(`atom '${id}' is bound to '${n.binder}' which is outside the selection`)
    }
  }
  const takenRegionIds = new Set<string>(c.allRegions)
  const root = freshId(takenRegionIds, 'root')

  const regions: Record<RegionId, Region> = { [root]: { kind: 'sheet' } }
  const subtreeRootSet = new Set(sel.regions)
  for (const id of c.allRegions) {
    const r = d.regions[id]!
    if (r.kind === 'sheet') continue // impossible: subtree roots are non-root children
    // sel.region is never in allRegions (it is the anchor, not selected content)
    const parent = subtreeRootSet.has(id) ? root : r.parent
    regions[id] = r.kind === 'cut'
      ? { kind: 'cut', parent }
      : { kind: 'bubble', parent, arity: r.arity }
  }

  const nodes: Record<string, DiagramNode> = {}
  for (const id of c.allNodes) {
    const n = d.nodes[id]!
    const region = n.region === sel.region ? root : n.region
    nodes[id] = n.kind === 'term'
      ? { kind: 'term', region, term: n.term }
      : { kind: 'atom', region, binder: n.binder }
  }

  const wires: Record<WireId, Wire> = {}
  const takenWireIds = new Set<string>(c.internalWires)
  for (const id of c.internalWires) {
    const w = d.wires[id]!
    wires[id] = {
      scope: w.scope === sel.region ? root : w.scope,
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
  return Object.freeze({ pattern, attachments: Object.freeze(attachments) })
}
