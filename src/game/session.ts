import { applyDoubleCutIntro } from '../kernel/rules/doublecut'
import { snapshotFromDiagram } from './diagram-snapshot'
import type { GameTree } from './model'
import type { Entity } from '../view3d/scene'

export type PointedTreePart = {
  readonly treeId: string
  readonly entity: Entity
  readonly distance: number
}

export type TreeMutation = {
  readonly treeId: string
  readonly before: GameTree
  readonly after: GameTree
}

const preparedSessionCommit: unique symbol = Symbol('prepared session commit')

export type PreparedSessionCommit = {
  readonly [preparedSessionCommit]: true
}

export type TreeMutationRenderer<Prepared> = {
  prepareTreeUpdate(mutation: TreeMutation): Prepared
  commitTreeUpdate(prepared: Prepared): void
  discardTreeUpdate(prepared: Prepared): void
}

export class ToolError extends Error {
  public constructor(message: string) {
    super(message)
    this.name = 'ToolError'
  }
}

export class GameSession {
  private prepared: PreparedSessionCommit | null = null
  private readonly preparedTrees = new WeakMap<PreparedSessionCommit, ReadonlyMap<string, GameTree>>()

  public constructor(private currentTrees: ReadonlyMap<string, GameTree>) {}

  public get trees(): ReadonlyMap<string, GameTree> {
    return this.currentTrees
  }

  public planDoubleCut(pointedPart: PointedTreePart): TreeMutation {
    const tree = this.trees.get(pointedPart.treeId)
    if (tree === undefined) throw new ToolError(`unknown tree '${pointedPart.treeId}'`)
    if (pointedPart.entity.kind !== 'branch') throw new ToolError('double cut requires a branch')
    const after = applyDoubleCutIntro(tree.snapshot.diagram, {
      region: pointedPart.entity.region,
      regions: [],
      nodes: [],
      wires: [],
    })
    const afterSnapshot = snapshotFromDiagram(after)
    return {
      treeId: tree.id,
      before: tree,
      after: { ...tree, snapshot: afterSnapshot },
    }
  }

  public prepare(mutation: TreeMutation): PreparedSessionCommit {
    if (this.prepared !== null) throw new ToolError('tree mutation publication is already prepared')
    if (mutation.treeId !== mutation.before.id || mutation.treeId !== mutation.after.id) {
      throw new ToolError('tree mutation identity is inconsistent')
    }
    if (this.trees.get(mutation.treeId) !== mutation.before) {
      throw new ToolError(`tree '${mutation.treeId}' changed since mutation was planned`)
    }
    const trees = new Map(this.trees)
    trees.set(mutation.treeId, mutation.after)
    const prepared: PreparedSessionCommit = { [preparedSessionCommit]: true }
    this.prepared = prepared
    this.preparedTrees.set(prepared, trees)
    return prepared
  }

  public commit(prepared: PreparedSessionCommit): void {
    if (this.prepared !== prepared) return
    const trees = this.preparedTrees.get(prepared)
    if (trees === undefined) return
    this.prepared = null
    this.preparedTrees.delete(prepared)
    this.currentTrees = trees
  }

  public discard(prepared: PreparedSessionCommit): void {
    if (this.prepared === prepared) {
      this.prepared = null
      this.preparedTrees.delete(prepared)
    }
  }
}

export function gameSession(trees: ReadonlyMap<string, GameTree>): GameSession { return new GameSession(trees) }

export function publishTreeMutation<Prepared>(
  session: GameSession,
  mutation: TreeMutation,
  renderer: TreeMutationRenderer<Prepared>,
  acceptSave: (tree: GameTree) => void,
): void {
  const preparedSession = session.prepare(mutation)
  let preparedRenderer: Prepared
  try {
    preparedRenderer = renderer.prepareTreeUpdate(mutation)
  } catch (error) {
    session.discard(preparedSession)
    throw error
  }
  try {
    acceptSave(mutation.after)
  } catch (error) {
    try {
      renderer.discardTreeUpdate(preparedRenderer)
    } catch {
      // The save-acceptance error is authoritative; renderer cleanup must not mask it.
    } finally {
      session.discard(preparedSession)
    }
    throw error
  }
  session.commit(preparedSession)
  renderer.commitTreeUpdate(preparedRenderer)
}
