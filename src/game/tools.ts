import type { GameTree } from './model'
import type { RegionId } from '../kernel/diagram/diagram'
import { derivedScope } from '../kernel/diagram/regions'
import {
  mkSelection,
  selectionContents,
  type SubgraphSelection,
} from '../kernel/diagram/subgraph/selection'

export type ToolId = 'sprout-spawner' | 'double-cut' | 'iteration'

type ToolCategory = '1'

export type ToolDefinition = {
  readonly id: ToolId
  readonly label: string
  readonly category: ToolCategory
  readonly capacityRequired: number
  readonly color: string
  readonly silhouette: 'sprout' | 'nested-cuts' | 'loop'
}

export const TOOL_CATALOG: readonly ToolDefinition[] = [
  {
    id: 'sprout-spawner',
    label: 'Sprout Spawner',
    category: '1',
    capacityRequired: 1,
    color: '#8cbf26',
    silhouette: 'sprout',
  },
  {
    id: 'double-cut',
    label: 'Double Cut',
    category: '1',
    capacityRequired: 0,
    color: '#d76f3f',
    silhouette: 'nested-cuts',
  },
  {
    id: 'iteration',
    label: 'Iteration',
    category: '1',
    capacityRequired: 0,
    color: '#7166c9',
    silhouette: 'loop',
  },
]

const SELECTOR_DURATION_MS = 1800

export type CategorySelection = {
  readonly category: ToolCategory
  readonly acquired: readonly ToolId[]
  readonly selected: ToolId
}

export type IterationCutting = {
  readonly sourceTree: GameTree
  readonly selection: SubgraphSelection
  readonly kind: 'whole' | 'subtree'
}

function definitionFor(id: string): ToolDefinition {
  const definition = TOOL_CATALOG.find((candidate) => candidate.id === id)
  if (definition === undefined) throw new Error(`unknown tool '${id}'`)
  return definition
}

export class ToolInventory {
  private readonly acquired = new Set<ToolId>()
  private readonly selectedByCategory = new Map<ToolCategory, ToolId>()
  private held: IterationCutting | null = null
  private selectorCategory: ToolCategory | null = null
  private selectorExpiresAt: number | null = null

  public constructor(
    acquiredToolIds: ReadonlySet<string>,
    private readonly clock: () => number = () => performance.now(),
  ) {
    for (const id of acquiredToolIds) this.acquired.add(definitionFor(id).id)
    for (const category of this.categories()) {
      const acquired = this.acquiredInCategory(category)
      if (acquired.length > 0) this.selectedByCategory.set(category, acquired[0]!)
    }
  }

  public get selector(): CategorySelection | null {
    return this.selectorAt(this.clock())
  }

  public get cutting(): IterationCutting | null {
    return this.held
  }

  public acquiredInCategory(category: ToolCategory): readonly ToolId[] {
    return TOOL_CATALOG
      .filter((definition) => definition.category === category && this.acquired.has(definition.id))
      .map((definition) => definition.id)
  }

  public selected(category: ToolCategory): ToolId {
    const selected = this.selectedByCategory.get(category)
    if (selected === undefined) throw new Error(`no acquired tool in category '${category}'`)
    return selected
  }

  public acquire(id: ToolId, reputation: number): void {
    const definition = definitionFor(id)
    if (this.acquired.has(definition.id)) throw new Error(`tool '${id}' is already acquired`)
    if (!Number.isSafeInteger(reputation) || reputation < 0) {
      throw new Error('reputation capacity must be a nonnegative safe integer')
    }
    if (reputation < definition.capacityRequired) {
      throw new Error(`tool '${id}' requires ${definition.capacityRequired} reputation capacity`)
    }
    this.acquired.add(definition.id)
    this.setSelection(definition.category, definition.id)
  }

  public cycle(category: ToolCategory, now: number = this.clock()): CategorySelection {
    const acquired = this.acquiredInCategory(category)
    if (acquired.length === 0) throw new Error(`no acquired tool in category '${category}'`)
    const selected = this.selected(category)
    const next = acquired[(acquired.indexOf(selected) + 1) % acquired.length]!
    this.setSelection(category, next)
    this.selectorCategory = category
    this.selectorExpiresAt = now + SELECTOR_DURATION_MS
    return this.categorySelection(category)
  }

  public selectorAt(now: number): CategorySelection | null {
    if (
      this.selectorCategory === null
      || this.selectorExpiresAt === null
      || now >= this.selectorExpiresAt
    ) return null
    return this.categorySelection(this.selectorCategory)
  }

  public snapshotForSave(): readonly ToolId[] {
    return TOOL_CATALOG
      .filter((definition) => this.acquired.has(definition.id))
      .map((definition) => definition.id)
  }

  public hold(cutting: IterationCutting): void {
    this.held = cutting
  }

  public cancel(): void {
    this.held = null
  }

  private categories(): readonly ToolCategory[] {
    return [...new Set(TOOL_CATALOG.map((definition) => definition.category))]
  }

  private setSelection(category: ToolCategory, next: ToolId): void {
    const previous = this.selectedByCategory.get(category)
    this.selectedByCategory.set(category, next)
    if (previous === 'iteration' && next !== 'iteration') this.cancel()
  }

  private categorySelection(category: ToolCategory): CategorySelection {
    return {
      category,
      acquired: this.acquiredInCategory(category),
      selected: this.selected(category),
    }
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
