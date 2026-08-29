import { describe, expect, it } from 'vitest'
import { snapshotFromDiagram } from '../../src/game/diagram-snapshot'
import type { GameTree } from '../../src/game/model'
import { ToolState, completeBranchCutting } from '../../src/game/tools'
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

describe('iteration tool state', () => {
  it('swaps equipped items and clears a held cutting', () => {
    const { tree, cut } = sourceTree()
    const cutting = completeBranchCutting(tree, cut)
    const tools = new ToolState()

    expect(tools.item).toBe('double-cut')
    expect(tools.swap()).toBe('iteration')
    tools.hold(cutting)
    expect(tools.cutting).toBe(cutting)
    expect(tools.swap()).toBe('double-cut')
    expect(tools.cutting).toBeNull()
  })

  it('cancels held state idempotently without changing the equipped item', () => {
    const { tree, cut } = sourceTree()
    const tools = new ToolState()
    tools.swap()
    tools.hold(completeBranchCutting(tree, cut))

    tools.cancel()
    tools.cancel()

    expect(tools.item).toBe('iteration')
    expect(tools.cutting).toBeNull()
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
