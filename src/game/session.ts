import type { Diagram } from '../kernel/diagram'
import { diagramToJson } from '../kernel/diagram'
import { applyDoubleCutIntro } from '../kernel/rules/doublecut'
import type { GameTree } from './model'
import type { TreeUpdate } from './save-client'
import type { Entity } from '../view3d/scene'

export type PointedTreePart = {
  readonly treeId: string
  readonly entity: Entity
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

export class GameSession {
  public constructor(public trees: ReadonlyMap<string, GameTree>) {}

  public applyDoubleCut(pointedPart: PointedTreePart): TreeMutation {
    const tree = this.trees.get(pointedPart.treeId)
    if (tree === undefined) throw new ToolError(`unknown tree '${pointedPart.treeId}'`)
    if (pointedPart.entity.kind !== 'branch') throw new ToolError('double cut requires a branch')
    const after = applyDoubleCutIntro(tree.diagram, {
      region: pointedPart.entity.region,
      regions: [],
      nodes: [],
      wires: [],
    })
    const afterJson = JSON.stringify(diagramToJson(after))
    const trees = new Map(this.trees)
    trees.set(tree.id, { ...tree, diagram: after, diagramJson: afterJson })
    this.trees = trees
    return { treeId: tree.id, before: tree.diagram, beforeJson: tree.diagramJson, after, afterJson }
  }
}

export function gameSession(trees: ReadonlyMap<string, GameTree>): GameSession { return new GameSession(trees) }

export type DoubleCutEffects = {
  readonly beginTreeTween: (treeId: string, before: Diagram, after: Diagram) => void
  readonly persistTree: (update: TreeUpdate) => void
}

export function useDoubleCut(
  session: GameSession,
  pointedPart: PointedTreePart,
  effects: DoubleCutEffects,
): TreeMutation {
  const mutation = session.applyDoubleCut(pointedPart)
  const tree = session.trees.get(mutation.treeId)
  if (tree === undefined) throw new Error(`mutated tree '${mutation.treeId}' is missing`)
  effects.beginTreeTween(tree.id, mutation.before, mutation.after)
  effects.persistTree({
    treeId: tree.id,
    diagramJson: mutation.afterJson,
    x: tree.placement.x,
    z: tree.placement.z,
    yaw: tree.placement.yaw,
  })
  return mutation
}
