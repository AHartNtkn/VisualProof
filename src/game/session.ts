import type { Diagram } from '../kernel/diagram'
import { diagramToJson } from '../kernel/diagram'
import { applyDoubleCutIntro } from '../kernel/rules/doublecut'
import { INTERACTION_REACH } from './camera'
import type { FreeCameraPose, GameWorld } from './model'
import type { TreeUpdate } from './save-client'

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

export type DoubleCutEffects = {
  readonly beginTreeTween: (
    treeId: string,
    before: Diagram,
    after: Diagram,
    now: number,
  ) => void
  readonly persistTree: (update: TreeUpdate) => void
}

export function useDoubleCut(
  session: GameSession,
  pointedPart: PointedTreePart,
  now: number,
  effects: DoubleCutEffects,
): TreeMutation {
  const camera = session.camera
  const mutation = session.applyDoubleCut(pointedPart)
  const tree = session.world.trees.get(mutation.treeId)
  if (tree === undefined) throw new Error(`mutated tree '${mutation.treeId}' is missing`)
  effects.beginTreeTween(tree.id, mutation.before, mutation.after, now)
  effects.persistTree({
    treeId: tree.id,
    diagramJson: mutation.afterJson,
    x: tree.placement.x,
    z: tree.placement.z,
    yaw: tree.placement.yaw,
  })
  if (session.camera !== camera) throw new Error('tool use changed camera state')
  return mutation
}
