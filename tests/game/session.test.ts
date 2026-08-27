import { describe, expect, it } from 'vitest'
import type { GameTree, GameWorld } from '../../src/game/model'
import type { TreeUpdate } from '../../src/game/save-client'
import { gameSession, useDoubleCut } from '../../src/game/session'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import type { Diagram } from '../../src/kernel/diagram/diagram'
import { diagramToJson } from '../../src/kernel/diagram/json'

const blankDiagram = new DiagramBuilder().build()

const largeBuilder = new DiagramBuilder()
const outerRegion = largeBuilder.cut(largeBuilder.root)
const nestedRegion = largeBuilder.cut(outerRegion)
largeBuilder.point(nestedRegion)
const largeDiagram = largeBuilder.build()

function tree(id: string, diagram: Diagram): GameTree {
  return {
    id,
    diagram,
    diagramJson: JSON.stringify(diagramToJson(diagram)),
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
    diagramJson: entry.diagramJson,
    placement: entry.placement,
  }))
}

describe('game tool session', () => {
  it('spawns a real empty double cut on the pointed branch of any generic tree', () => {
    const session = gameSession(worldWithTree('large', largeDiagram).trees)
    const mutation = session.applyDoubleCut({
      treeId: 'large', entityKey: `b:${nestedRegion}`, distance: 12,
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
    expect(mutation.afterJson).toBe(JSON.stringify(diagramToJson(mutation.after)))
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
      treeId: 'tree-a', entityKey: 'r:n0', distance: 5,
    })).toThrow(/branch/)
    expect(() => session.applyDoubleCut({
      treeId: 'missing', entityKey: 'b:r0', distance: 5,
    })).toThrow(/unknown tree/)
    expect(treeValues(session.trees)).toEqual(beforeTrees)
  })

  it('changes and persists only the pointed generic tree', () => {
    const world = worldWithTree('large', largeDiagram)
    const untouched = tree('other', blankDiagram)
    const session = gameSession(new Map([...world.trees, ['other', untouched]]))
    const treesBefore = treeValues(session.trees)
    const tweens: Array<{ readonly treeId: string; readonly beforeJson: string; readonly afterJson: string; readonly now: number }> = []
    const writes: TreeUpdate[] = []

    const mutation = useDoubleCut(
      session,
      { treeId: 'large', entityKey: `b:${nestedRegion}`, distance: 12 },
      250,
      {
        beginTreeTween: (treeId, before, after, now) => tweens.push({
          treeId,
          beforeJson: JSON.stringify(diagramToJson(before)),
          afterJson: JSON.stringify(diagramToJson(after)),
          now,
        }),
        persistTree: (update) => writes.push(update),
      },
    )

    expect(tweens).toEqual([{
      treeId: 'large', beforeJson: mutation.beforeJson, afterJson: mutation.afterJson, now: 250,
    }])
    expect(writes).toEqual([{
      treeId: 'large', diagramJson: mutation.afterJson, x: 0, z: -20, yaw: 0,
    }])
    expect(treeValues(session.trees)).toEqual([
      { id: 'large', diagramJson: mutation.afterJson, placement: { x: 0, z: -20, yaw: 0 } },
      { id: 'other', diagramJson: untouched.diagramJson, placement: untouched.placement },
    ])
    expect(treeValues(session.trees).filter(({ id }) => id === 'other')).toEqual(
      treesBefore.filter(({ id }) => id === 'other'),
    )
  })
})
