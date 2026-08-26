import type { Diagram } from '../kernel/diagram'
import { diagramToJson } from '../kernel/diagram'
import { applyDoubleCutIntro } from '../kernel/rules/doublecut'
import { INTERACTION_REACH } from './camera'
import type { FreeCameraPose, GameWorld } from './model'

export type PointedTreePart = {
  readonly treeId: string
  readonly entityKey: string
  readonly distance: number
}

export type TreeMutation = {
  readonly treeId: string
  readonly before: Diagram
  readonly beforeJson: string
  readonly after: Diagram
  readonly afterJson: string
}

export class ToolError extends Error {
  public constructor(message: string) {
    super(message)
    this.name = 'ToolError'
  }
}

function branchRegion(key: string): string {
  if (!key.startsWith('b:') || key.length === 2) {
    throw new ToolError('double cut requires a branch')
  }
  return key.slice(2)
}

export class GameSession {
  public constructor(public world: GameWorld) {}

  public get camera(): FreeCameraPose {
    return this.world.camera
  }

  public applyDoubleCut(pointedPart: PointedTreePart): TreeMutation {
    if (!Number.isFinite(pointedPart.distance) || pointedPart.distance > INTERACTION_REACH) {
      throw new ToolError(`double cut target is beyond interaction reach ${INTERACTION_REACH}`)
    }
    const tree = this.world.trees.get(pointedPart.treeId)
    if (tree === undefined) throw new ToolError(`unknown tree '${pointedPart.treeId}'`)

    const after = applyDoubleCutIntro(tree.diagram, {
      region: branchRegion(pointedPart.entityKey),
      regions: [],
      nodes: [],
      wires: [],
    })
    const afterJson = JSON.stringify(diagramToJson(after))
    const trees = new Map(this.world.trees)
    trees.set(tree.id, { ...tree, diagram: after, diagramJson: afterJson })
    this.world = { ...this.world, trees }
    return {
      treeId: tree.id,
      before: tree.diagram,
      beforeJson: tree.diagramJson,
      after,
      afterJson,
    }
  }
}

export function gameSession(world: GameWorld): GameSession {
  return new GameSession(world)
}
