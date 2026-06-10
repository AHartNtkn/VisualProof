import type { Diagram, NodeId, RegionId, WireId } from '../diagram'
import { DiagramError } from '../diagram'
import type { DiagramWithBoundary } from '../boundary'
import type { Occurrence } from './match'
import type { SubgraphSelection } from './selection'
import { mkSelection } from './selection'

/**
 * Convert a matcher occurrence into the selection of its host subgraph —
 * the form removeSubgraph/extractSubgraph consume. Boundary wires are
 * EXCLUDED: Occurrence.wireMap maps them to the attachment wires, which are
 * the seam to the surrounding diagram, not occurrence content. Selecting one
 * whose endpoints all lie inside the occurrence would validate and then be
 * DELETED by removal instead of trimmed — a silently wrong rule application.
 */
export function occurrenceToSelection(
  host: Diagram,
  pattern: DiagramWithBoundary,
  occ: Occurrence,
): SubgraphSelection {
  const pd = pattern.diagram
  const boundary = new Set(pattern.boundary)
  const regions: RegionId[] = []
  for (const [pr, r] of Object.entries(pd.regions)) {
    if (r.kind === 'sheet' || r.parent !== pd.root) continue
    const img = occ.regionMap.get(pr)
    if (img === undefined) throw new DiagramError(`occurrence is missing an image for pattern region '${pr}'`)
    regions.push(img)
  }
  const nodes: NodeId[] = []
  for (const [pn, n] of Object.entries(pd.nodes)) {
    if (n.region !== pd.root) continue
    const img = occ.nodeMap.get(pn)
    if (img === undefined) throw new DiagramError(`occurrence is missing an image for pattern node '${pn}'`)
    nodes.push(img)
  }
  const wires: WireId[] = []
  for (const [pw, w] of Object.entries(pd.wires)) {
    if (boundary.has(pw) || w.scope !== pd.root) continue
    const img = occ.wireMap.get(pw)
    if (img === undefined) throw new DiagramError(`occurrence is missing an image for pattern wire '${pw}'`)
    wires.push(img)
  }
  regions.sort()
  nodes.sort()
  wires.sort()
  return mkSelection(host, { region: occ.region, regions, nodes, wires })
}
