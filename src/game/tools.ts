import type { GameTree } from './model'
import type { RegionId } from '../kernel/diagram/diagram'
import { derivedScope } from '../kernel/diagram/regions'
import {
  mkSelection,
  selectionContents,
  type SubgraphSelection,
} from '../kernel/diagram/subgraph/selection'

export type EquippedItem = 'double-cut' | 'iteration'

export type IterationCutting = {
  readonly sourceTree: GameTree
  readonly selection: SubgraphSelection
  readonly kind: 'whole' | 'subtree'
}

export class ToolState {
  private equipped: EquippedItem = 'double-cut'
  private held: IterationCutting | null = null

  public get item(): EquippedItem {
    return this.equipped
  }

  public get cutting(): IterationCutting | null {
    return this.held
  }

  public swap(): EquippedItem {
    this.equipped = this.equipped === 'double-cut' ? 'iteration' : 'double-cut'
    this.cancel()
    return this.equipped
  }

  public hold(cutting: IterationCutting): void {
    this.held = cutting
  }

  public cancel(): void {
    this.held = null
  }
}

export function completeBranchCutting(
  sourceTree: GameTree,
  region: RegionId,
): IterationCutting {
  const diagram = sourceTree.snapshot.diagram
  const branch = diagram.regions[region]
  if (branch === undefined) throw new Error(`unknown branch region '${region}'`)

  if (region !== diagram.root) {
    if (branch.kind !== 'cut') throw new Error(`branch region '${region}' is not a cut`)
    return {
      sourceTree,
      kind: 'subtree',
      selection: mkSelection(diagram, {
        region: branch.parent,
        regions: [region],
        nodes: [],
        wires: [],
      }),
    }
  }

  const regions = Object.entries(diagram.regions)
    .filter(([, candidate]) => candidate.kind === 'cut' && candidate.parent === diagram.root)
    .map(([id]) => id)
    .sort()
  const nodes = Object.entries(diagram.nodes)
    .filter(([, node]) => node.region === diagram.root)
    .map(([id]) => id)
    .sort()
  const partial = mkSelection(diagram, {
    region: diagram.root,
    regions,
    nodes,
    wires: [],
  })
  const selectedNodes = selectionContents(diagram, partial).allNodes
  const wires = Object.entries(diagram.wires)
    .filter(([id, wire]) =>
      derivedScope(diagram, id) === diagram.root
      && wire.endpoints.every((endpoint) => selectedNodes.has(endpoint.node)),
    )
    .map(([id]) => id)
    .sort()
  return {
    sourceTree,
    kind: 'whole',
    selection: mkSelection(diagram, { region: diagram.root, regions, nodes, wires }),
  }
}
