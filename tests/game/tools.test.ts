import { describe, expect, it } from 'vitest'
import { snapshotFromDiagram } from '../../src/game/diagram-snapshot'
import type { GameTree } from '../../src/game/model'
import { TOOL_CATALOG, ToolInventory, completeBranchCutting } from '../../src/game/tools'
import { LiveToolContent, decodeToolContent, openingToolContent } from '../../src/game/tools/content'
import { readFileSync } from 'node:fs'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { derivedScope } from '../../src/kernel/diagram/regions'
import { selectionContents } from '../../src/kernel/diagram/subgraph/selection'
import { IOTA } from '../../src/kernel/diagram/sig'

function sourceTree(): { readonly tree: GameTree; readonly cut: string } {
  const builder = new DiagramBuilder()
  const cut = builder.cut(builder.root)
  builder.identity(builder.root, IOTA, 2)
  builder.point(cut)
  const diagram = builder.build()
  return {
    tree: {
      id: 'source',
      snapshot: snapshotFromDiagram(diagram),
      placement: { x: 0, z: -20, yaw: 0 },
    },
    cut,
  }
}

describe('tool inventory', () => {
  it('resolves the legacy display label through the live content revision', () => {
    // Catches the mechanics catalog retaining a copied editable tool name.
    const original = openingToolContent.current
    const records: Array<Record<string, unknown>> = JSON.parse(readFileSync(
      new URL('../../game/content/tools.json', import.meta.url),
      'utf8',
    ))
    records[2]!['name'] = 'Branch Copier'

    try {
      openingToolContent.publish(decodeToolContent(records))
      expect(TOOL_CATALOG.find(({ id }) => id === 'iteration')?.label).toBe('Branch Copier')
    } finally {
      openingToolContent.publish(original)
    }
  })

  it('keeps cycling keyed by tool IDs when live copy changes', () => {
    // Catches inventory selection deriving its behavior from editable tool labels.
    const records: Array<Record<string, unknown>> = JSON.parse(readFileSync(
      new URL('../../game/content/tools.json', import.meta.url),
      'utf8',
    ))
    records[2]!['name'] = 'Branch Copier'
    const content = new LiveToolContent(decodeToolContent(records))
    const inventory = new ToolInventory(new Set(['sprout-spawner', 'iteration']))

    expect(content.current.definition('iteration').name).toBe('Branch Copier')
    expect(inventory.cycle('1', 100).selected).toBe('iteration')
    expect(inventory.snapshotForSave()).toEqual(['sprout-spawner', 'iteration'])
  })
  it('cycles acquired tools in authored category order', () => {
    const inventory = new ToolInventory(new Set(['sprout-spawner']))

    expect(inventory.selected('1')).toBe('sprout-spawner')
    expect(inventory.cycle('1', 100).selected).toBe('sprout-spawner')

    inventory.acquire('double-cut', 0)
    expect(inventory.selected('1')).toBe('double-cut')
    inventory.acquire('iteration', 0)
    expect(inventory.selected('1')).toBe('iteration')
    expect(inventory.acquiredInCategory('1')).toEqual([
      'sprout-spawner', 'double-cut', 'iteration',
    ])
    expect(inventory.cycle('1', 200).selected).toBe('sprout-spawner')
    expect(inventory.cycle('1', 300).selected).toBe('double-cut')
    expect(inventory.cycle('1', 400).selected).toBe('iteration')
  })

  it('hides unacquired tools from category selection and save snapshots', () => {
    const inventory = new ToolInventory(new Set(['sprout-spawner', 'iteration']))

    expect(inventory.acquiredInCategory('1')).toEqual(['sprout-spawner', 'iteration'])
    expect(inventory.cycle('1', 10).selected).toBe('iteration')
    expect(inventory.cycle('1', 20).selected).toBe('sprout-spawner')
    expect(inventory.snapshotForSave()).toEqual(['sprout-spawner', 'iteration'])
  })

  it('rejects acquisition below a tool capacity requirement', () => {
    const inventory = new ToolInventory(new Set())

    expect(() => inventory.acquire('sprout-spawner', 0)).toThrow(/capacity/i)
    inventory.acquire('sprout-spawner', 1)
    expect(inventory.snapshotForSave()).toEqual(['sprout-spawner'])
  })

  it('rejects duplicate acquisition without changing selection or saves', () => {
    const inventory = new ToolInventory(new Set(['sprout-spawner']))

    expect(() => inventory.acquire('sprout-spawner', 1)).toThrow(/already acquired/i)
    expect(inventory.selected('1')).toBe('sprout-spawner')
    expect(inventory.snapshotForSave()).toEqual(['sprout-spawner'])
  })

  it('selects a newly acquired tool without opening a selector', () => {
    const inventory = new ToolInventory(new Set(['sprout-spawner']))

    inventory.acquire('double-cut', 0)

    expect(inventory.selected('1')).toBe('double-cut')
    expect(inventory.selectorAt(0)).toBeNull()
  })

  it('expires a category selector exactly 1800ms after its last cycle without changing selection', () => {
    const inventory = new ToolInventory(new Set(['sprout-spawner', 'double-cut']))

    const selection = inventory.cycle('1', 100)

    expect(selection).toMatchObject({ category: '1', selected: 'double-cut' })
    expect(inventory.selectorAt(1899)).toMatchObject({ selected: 'double-cut' })
    expect(inventory.selectorAt(1900)).toBeNull()
    expect(inventory.selected('1')).toBe('double-cut')
  })

  it('clears a held cutting when selecting away from Iteration', () => {
    const { tree, cut } = sourceTree()
    const cutting = completeBranchCutting(tree, cut)
    const inventory = new ToolInventory(new Set(['sprout-spawner', 'iteration']))

    expect(inventory.cycle('1', 0).selected).toBe('iteration')
    inventory.hold(cutting)
    expect(inventory.cutting).toBe(cutting)
    expect(inventory.cycle('1', 1).selected).toBe('sprout-spawner')
    expect(inventory.cutting).toBeNull()
  })

  it('cancels held state idempotently without changing the equipped item', () => {
    const { tree, cut } = sourceTree()
    const inventory = new ToolInventory(new Set(['sprout-spawner', 'iteration']))
    inventory.cycle('1', 0)
    inventory.hold(completeBranchCutting(tree, cut))

    inventory.cancel()
    inventory.cancel()

    expect(inventory.selected('1')).toBe('iteration')
    expect(inventory.cutting).toBeNull()
  })

  it('cuts a non-root branch as exactly one complete subtree selection', () => {
    const { tree, cut } = sourceTree()

    const cutting = completeBranchCutting(tree, cut)
    const contents = selectionContents(tree.snapshot.diagram, cutting.selection)

    expect(cutting).toMatchObject({ sourceTree: tree, kind: 'subtree' })
    expect(cutting.selection).toEqual({
      region: tree.snapshot.diagram.root,
      regions: [cut],
      nodes: [],
      wires: [],
    })
    expect(contents.allRegions).toContain(cut)
    expect(contents.allNodes).toContain('n1')
  })

  it('cuts the root as every root-scoped part of the complete tree', () => {
    const { tree, cut } = sourceTree()
    const diagram = tree.snapshot.diagram

    const cutting = completeBranchCutting(tree, diagram.root)
    const contents = selectionContents(diagram, cutting.selection)

    expect(cutting.kind).toBe('whole')
    expect(cutting.selection.regions).toEqual([cut])
    expect(cutting.selection.nodes).toContain('n0')
    expect(cutting.selection.wires).toEqual(
      Object.keys(diagram.wires).filter((wire) => derivedScope(diagram, wire) === diagram.root).sort(),
    )
    expect(contents.allRegions.size).toBe(Object.keys(diagram.regions).length - 1)
    expect(contents.allNodes.size).toBe(Object.keys(diagram.nodes).length)
  })
})
