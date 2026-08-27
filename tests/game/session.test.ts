import { describe, expect, it } from 'vitest'
import type { GameTree, GameWorld } from '../../src/game/model'
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
    expect(session.trees.get('large')).toMatchObject({
      diagram: mutation.after,
      diagramJson: mutation.afterJson,
    })
    expect('camera' in session).toBe(false)
    expect('world' in session).toBe(false)
  })

  it('rejects non-branches and unknown trees without mutation', () => {
    const session = gameSession(worldWithTree('tree-a', blankDiagram).trees)
    const beforeTrees = session.trees
    expect(() => session.applyDoubleCut({
      treeId: 'tree-a', entityKey: 'r:n0', distance: 5,
    })).toThrow(/branch/)
    expect(() => session.applyDoubleCut({
      treeId: 'missing', entityKey: 'b:r0', distance: 5,
    })).toThrow(/unknown tree/)
    expect(session.trees).toBe(beforeTrees)
    expect(session.trees.get('tree-a')!.diagram).toBe(blankDiagram)
  })

  it('changes and persists only the pointed generic tree', () => {
    const world = worldWithTree('large', largeDiagram)
    const untouched = tree('other', blankDiagram)
    const session = gameSession(new Map([...world.trees, ['other', untouched]]))
    const tweens: Array<{ readonly treeId: string; readonly now: number }> = []
    const writes: Array<{ readonly treeId: string; readonly diagramJson: string }> = []

    const mutation = useDoubleCut(
      session,
      { treeId: 'large', entityKey: `b:${nestedRegion}`, distance: 12 },
      250,
      {
        beginTreeTween: (treeId, _before, _after, now) => tweens.push({ treeId, now }),
        persistTree: ({ treeId, diagramJson }) => writes.push({ treeId, diagramJson }),
      },
    )

    expect(tweens).toEqual([{ treeId: 'large', now: 250 }])
    expect(writes).toEqual([{ treeId: 'large', diagramJson: mutation.afterJson }])
    expect(session.trees.get('large')?.diagram).toBe(mutation.after)
    expect(session.trees.get('other')).toEqual(untouched)
    expect('camera' in session).toBe(false)
    expect('world' in session).toBe(false)
  })
})
