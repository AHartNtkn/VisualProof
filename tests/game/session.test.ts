import { describe, expect, it } from 'vitest'
import { INTERACTION_REACH } from '../../src/game/camera'
import type { GameTree, GameWorld } from '../../src/game/model'
import { gameSession } from '../../src/game/session'
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
    const session = gameSession(worldWithTree('large', largeDiagram))
    const beforeCamera = session.camera
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
    expect(session.world.trees.get('large')).toMatchObject({
      diagram: mutation.after,
      diagramJson: mutation.afterJson,
    })
    expect(session.camera).toBe(beforeCamera)
  })

  it('rejects non-branches, unknown trees, and pointed parts beyond 100 without mutation', () => {
    const session = gameSession(worldWithTree('tree-a', blankDiagram))
    const beforeWorld = session.world
    expect(() => session.applyDoubleCut({
      treeId: 'tree-a', entityKey: 'r:n0', distance: 5,
    })).toThrow(/branch/)
    expect(() => session.applyDoubleCut({
      treeId: 'missing', entityKey: 'b:r0', distance: 5,
    })).toThrow(/unknown tree/)
    expect(() => session.applyDoubleCut({
      treeId: 'tree-a', entityKey: 'b:r0', distance: INTERACTION_REACH + 0.001,
    })).toThrow(/reach/)
    expect(session.world).toBe(beforeWorld)
    expect(session.world.trees.get('tree-a')!.diagram).toBe(blankDiagram)
  })

  it('accepts the strict reach boundary', () => {
    const session = gameSession(worldWithTree('tree-a', blankDiagram))

    expect(() => session.applyDoubleCut({
      treeId: 'tree-a', entityKey: 'b:r0', distance: INTERACTION_REACH,
    })).not.toThrow()
  })
})
