import { DiagramBuilder } from '../kernel/diagram/builder'
import { citeLibraryProposition, libraryProposition } from '../kernel/proof/library'
import { applyDoubleCutIntro } from '../kernel/rules/doublecut'
import { applyIteration } from '../kernel/rules/iteration'
import { snapshotFromDiagram } from './diagram-snapshot'
import type { GameTree } from './model'
import type { IterationCutting } from './tools'
import type { Entity } from '../view3d/scene'

export type PointedTreePart = {
  readonly treeId: string
  readonly entity: Entity
  readonly distance: number
}

export type TreeChange =
  | {
    readonly kind: 'update'
    readonly treeId: string
    readonly before: GameTree
    readonly after: GameTree
  }
  | {
    readonly kind: 'insert'
    readonly treeId: string
    readonly after: GameTree
  }

type TreeUpdate = Extract<TreeChange, { readonly kind: 'update' }>
type TreeInsert = Extract<TreeChange, { readonly kind: 'insert' }>

const preparedSessionCommit: unique symbol = Symbol('prepared session commit')

export type PreparedSessionCommit = {
  readonly [preparedSessionCommit]: true
}

export type TreeChangeRenderer<Prepared> = {
  prepareTreeChange(change: TreeChange): Prepared
  commitTreeChange(prepared: Prepared): void
  discardTreeChange(prepared: Prepared): void
}

export class ToolError extends Error {
  public constructor(message: string) {
    super(message)
    this.name = 'ToolError'
  }
}

const blankDiagram = new DiagramBuilder().build()

export class GameSession {
  private prepared: PreparedSessionCommit | null = null
  private readonly preparedTrees = new WeakMap<PreparedSessionCommit, ReadonlyMap<string, GameTree>>()

  public constructor(
    private currentTrees: ReadonlyMap<string, GameTree>,
    private readonly newTreeId: () => string,
  ) {}

  public get trees(): ReadonlyMap<string, GameTree> {
    return this.currentTrees
  }

  public planDoubleCut(pointedPart: PointedTreePart): TreeUpdate {
    const tree = this.requirePointedBranch(pointedPart, 'double cut')
    const after = applyDoubleCutIntro(tree.snapshot.diagram, {
      region: pointedPart.entity.kind === 'branch' ? pointedPart.entity.region : tree.snapshot.diagram.root,
      regions: [],
      nodes: [],
      wires: [],
    })
    return this.update(tree, snapshotFromDiagram(after))
  }

  public planIteration(cutting: IterationCutting, target: PointedTreePart): TreeUpdate {
    this.requireCurrentCutting(cutting)
    const targetTree = this.requirePointedBranch(target, 'iteration')
    const targetRegion = target.entity.kind === 'branch'
      ? target.entity.region
      : targetTree.snapshot.diagram.root

    if (targetTree.id === cutting.sourceTree.id) {
      const after = applyIteration(
        cutting.sourceTree.snapshot.diagram,
        cutting.selection,
        targetRegion,
      )
      return this.update(cutting.sourceTree, snapshotFromDiagram(after))
    }
    if (cutting.kind !== 'whole') {
      throw new ToolError('cross-tree iteration requires a whole tree cutting')
    }
    const proposition = libraryProposition(cutting.sourceTree.id, cutting.sourceTree.snapshot.diagram)
    const after = citeLibraryProposition(targetTree.snapshot.diagram, proposition, targetRegion)
    return this.update(targetTree, snapshotFromDiagram(after))
  }

  public planDuplicate(
    cutting: IterationCutting,
    placement: GameTree['placement'],
  ): TreeInsert {
    this.requireCurrentCutting(cutting)
    if (cutting.kind !== 'whole') {
      throw new ToolError('tree duplication requires a whole tree cutting')
    }
    const treeId = this.newTreeId()
    if (this.trees.has(treeId)) throw new ToolError(`tree '${treeId}' already exists`)
    const proposition = libraryProposition(cutting.sourceTree.id, cutting.sourceTree.snapshot.diagram)
    const diagram = citeLibraryProposition(blankDiagram, proposition, blankDiagram.root)
    const after: GameTree = {
      id: treeId,
      snapshot: snapshotFromDiagram(diagram),
      placement: { ...placement },
    }
    return { kind: 'insert', treeId, after }
  }

  public prepare(change: TreeChange): PreparedSessionCommit {
    if (this.prepared !== null) throw new ToolError('tree change publication is already prepared')
    if (change.treeId !== change.after.id) {
      throw new ToolError('tree change identity is inconsistent')
    }
    if (change.kind === 'update') {
      if (change.treeId !== change.before.id) {
        throw new ToolError('tree change identity is inconsistent')
      }
      if (this.trees.get(change.treeId) !== change.before) {
        throw new ToolError(`tree '${change.treeId}' changed since change was planned`)
      }
    } else if (this.trees.has(change.treeId)) {
      throw new ToolError(`tree '${change.treeId}' already exists`)
    }
    const trees = new Map(this.trees)
    trees.set(change.treeId, change.after)
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

  private requireCurrentCutting(cutting: IterationCutting): void {
    if (this.trees.get(cutting.sourceTree.id) !== cutting.sourceTree) {
      throw new ToolError(`tree '${cutting.sourceTree.id}' changed since cutting was taken`)
    }
  }

  private requirePointedBranch(pointedPart: PointedTreePart, action: string): GameTree {
    const tree = this.trees.get(pointedPart.treeId)
    if (tree === undefined) throw new ToolError(`unknown tree '${pointedPart.treeId}'`)
    if (pointedPart.entity.kind !== 'branch') throw new ToolError(`${action} requires a branch`)
    return tree
  }

  private update(before: GameTree, snapshot: GameTree['snapshot']): TreeUpdate {
    return {
      kind: 'update',
      treeId: before.id,
      before,
      after: { ...before, snapshot },
    }
  }
}

export function gameSession(
  trees: ReadonlyMap<string, GameTree>,
  newTreeId: () => string = () => `tree-${crypto.randomUUID()}`,
): GameSession {
  return new GameSession(trees, newTreeId)
}

export function publishTreeChange<Prepared>(
  session: GameSession,
  change: TreeChange,
  renderer: TreeChangeRenderer<Prepared>,
  acceptSave: (tree: GameTree) => void,
): void {
  const preparedSession = session.prepare(change)
  let preparedRenderer: Prepared
  try {
    preparedRenderer = renderer.prepareTreeChange(change)
  } catch (error) {
    session.discard(preparedSession)
    throw error
  }
  try {
    acceptSave(change.after)
  } catch (error) {
    try {
      renderer.discardTreeChange(preparedRenderer)
    } catch {
      // The save-acceptance error is authoritative; renderer cleanup must not mask it.
    } finally {
      session.discard(preparedSession)
    }
    throw error
  }
  session.commit(preparedSession)
  renderer.commitTreeChange(preparedRenderer)
}
