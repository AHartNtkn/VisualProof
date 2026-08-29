import { describe, expect, it } from 'vitest'
import type { GameTree, GameWorld } from '../../src/game/model'
import { gameSession, useDoubleCut } from '../../src/game/session'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import type { Diagram } from '../../src/kernel/diagram/diagram'
import { snapshotFromDiagram } from '../../src/game/diagram-snapshot'
import { treeUpdateFromGameTree, type TreeUpdate } from '../../src/game/save-client'

const blankDiagram = new DiagramBuilder().build()

const largeBuilder = new DiagramBuilder()
const outerRegion = largeBuilder.cut(largeBuilder.root)
const nestedRegion = largeBuilder.cut(outerRegion)
largeBuilder.point(nestedRegion)
const largeDiagram = largeBuilder.build()

function tree(id: string, diagram: Diagram): GameTree {
  return {
    id,
    snapshot: snapshotFromDiagram(diagram),
    placement: { x: 0, z: -20, yaw: 0 },
  }
}

function worldWithTree(id: string, diagram: Diagram): GameWorld {
  return {
    slot: { id: 'slot-a', name: 'Slot A', updatedAtMs: 0 },
    camera: { position: { x: 0, y: 1.7, z: 0 }, yaw: 0, pitch: 0 },
    trees: new Map([[id, tree(id, diagram)]]),
  }
}

function newRegions(before: Diagram, after: Diagram): string[] {
  return Object.keys(after.regions).filter((id) => before.regions[id] === undefined)
}

function treeValues(trees: ReadonlyMap<string, GameTree>): readonly {
  readonly id: string
  readonly diagramJson: string
  readonly placement: GameTree['placement']
}[] {
  return [...trees.values()].map((entry) => ({
    id: entry.id,
    diagramJson: entry.snapshot.json,
    placement: entry.placement,
  }))
}

describe('game tool session', () => {
  it('persists the mutated snapshot and unchanged placement as one tree update', () => {
    const session = gameSession(worldWithTree('large', largeDiagram).trees)
    const persisted: TreeUpdate[] = []

    const mutation = useDoubleCut(session, {
      treeId: 'large',
      entity: {
        kind: 'branch', key: 'branch', region: nestedRegion,
        polarity: 0, pts: [],
      },
      distance: 12,
    }, {
      beginTreeTween() {},
      persistTree(update) { persisted.push(update) },
    })

    const liveTree = session.trees.get('large')!
    expect(persisted).toEqual([treeUpdateFromGameTree(liveTree)])
    expect(persisted[0]!.diagramJson).toBe(liveTree.snapshot.json)
    expect(persisted[0]).toEqual({
      treeId: 'large',
      diagramJson: liveTree.snapshot.json,
      x: 0,
      z: -20,
      yaw: 0,
    })
    expect(mutation.afterJson).toBe(liveTree.snapshot.json)
  })

  it('spawns a real empty double cut on the pointed branch of any generic tree', () => {
    const session = gameSession(worldWithTree('large', largeDiagram).trees)
    const mutation = session.applyDoubleCut({
      treeId: 'large',
      entity: {
        kind: 'branch', key: 'drawing-key-unrelated-to-region', region: nestedRegion,
        polarity: 0, pts: [],
      },
      distance: 12,
    })

    expect(Object.keys(mutation.after.regions)).toHaveLength(
      Object.keys(largeDiagram.regions).length + 2,
    )
    const outer = newRegions(mutation.before, mutation.after).find((id) => {
      const region = mutation.after.regions[id]!
      return region.kind === 'cut' && region.parent === nestedRegion
    })!
    const inner = newRegions(mutation.before, mutation.after).find((id) => {
      const region = mutation.after.regions[id]!
      return region.kind === 'cut' && region.parent === outer
    })!
    expect(mutation.after.regions[inner]).toEqual({ kind: 'cut', parent: outer })
    expect(mutation.afterJson).toBe(snapshotFromDiagram(mutation.after).json)
    expect(treeValues(session.trees)).toEqual([{
      id: 'large',
      diagramJson: mutation.afterJson,
      placement: { x: 0, z: -20, yaw: 0 },
    }])
  })

  it('rejects non-branches and unknown trees without mutation', () => {
    const session = gameSession(worldWithTree('tree-a', blankDiagram).trees)
    const beforeTrees = treeValues(session.trees)
    expect(() => session.applyDoubleCut({
      treeId: 'tree-a',
      entity: { kind: 'ring', key: 'r:n0', node: 'n0', headWire: null, pts: [] },
      distance: 5,
    })).toThrow(/branch/)
    expect(() => session.applyDoubleCut({
      treeId: 'missing',
      entity: { kind: 'branch', key: 'anything', region: 'r0', polarity: 0, pts: [] },
      distance: 5,
    })).toThrow(/unknown tree/)
    expect(treeValues(session.trees)).toEqual(beforeTrees)
  })
})
