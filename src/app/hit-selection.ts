import type { Diagram, NodeId, RegionId, WireId } from '../kernel/diagram/diagram'
import { derivedScope } from '../kernel/diagram/regions'
import type { SubgraphSelection } from '../kernel/diagram/subgraph/selection'
import { mkSelection } from '../kernel/diagram/subgraph/selection'

export type Hit =
  | { readonly kind: 'node'; readonly id: NodeId }
  | { readonly kind: 'region'; readonly id: RegionId }
  | { readonly kind: 'wire'; readonly id: WireId }

export function buildSelection(d: Diagram, items: readonly Hit[]): SubgraphSelection {
  const nodes: NodeId[] = []
  const regions: RegionId[] = []
  const wires: WireId[] = []
  const anchors = new Set<RegionId>()
  for (const item of items) {
    if (item.kind === 'node') {
      const node = d.nodes[item.id]
      if (node === undefined) throw new Error(`unknown node '${item.id}'`)
      nodes.push(item.id)
      anchors.add(node.region)
    } else if (item.kind === 'region') {
      const region = d.regions[item.id]
      if (region === undefined) throw new Error(`unknown region '${item.id}'`)
      if (region.kind === 'sheet') throw new Error('the sheet cannot be selected')
      regions.push(item.id)
      anchors.add(region.parent)
    } else {
      const wire = d.wires[item.id]
      if (wire === undefined) throw new Error(`unknown wire '${item.id}'`)
      wires.push(item.id)
      anchors.add(derivedScope(d, item.id))
    }
  }
  if (anchors.size === 0) throw new Error('nothing selected')
  if (anchors.size > 1) {
    throw new Error(
      `selection spans several regions (${[...anchors].map((anchor) => `'${anchor}'`).join(', ')}); `
      + 'select the enclosing cut instead of reaching inside it',
    )
  }
  return mkSelection(d, {
    region: [...anchors][0]!,
    regions,
    nodes,
    wires,
  })
}
