import * as THREE from 'three'
import type { scene3 } from '../../view3d/scene'
import { planTransition, sceneAt, type TweenPlan } from '../../view3d/transition'
import type { GameTreeRuntimeApi, RenderTree } from './runtime'
import { disposeTreeObject } from './tree-objects'

export const TREE_TWEEN_MS = 350

export type TreeRenderSnapshot = ReturnType<typeof scene3>

type TweenTrack = {
  readonly plan: TweenPlan
  readonly target: TreeRenderSnapshot
  readonly start: number
}

export class TreeTweenTracks {
  private readonly tracks = new Map<string, TweenTrack>()

  public begin(
    treeId: string,
    before: TreeRenderSnapshot,
    after: TreeRenderSnapshot,
    now: number,
  ): this {
    const current = this.tracks.get(treeId)
    const displayed = current === undefined
      ? before
      : sceneAt(current.plan, this.progress(current, now))
    this.tracks.set(treeId, {
      plan: planTransition(displayed, after),
      target: after,
      start: now,
    })
    return this
  }

  public has(treeId: string): boolean {
    return this.tracks.has(treeId)
  }

  public at(now: number): ReadonlyMap<string, TreeRenderSnapshot> {
    const frames = new Map<string, TreeRenderSnapshot>()
    for (const [treeId, track] of this.tracks) {
      const progress = this.progress(track, now)
      frames.set(treeId, progress === 1 ? track.target : sceneAt(track.plan, progress))
    }
    return frames
  }

  public takeCompleted(now: number): ReadonlyMap<string, TreeRenderSnapshot> {
    const completed = new Map<string, TreeRenderSnapshot>()
    for (const [treeId, track] of this.tracks) {
      if (this.progress(track, now) < 1) continue
      completed.set(treeId, track.target)
      this.tracks.delete(treeId)
    }
    return completed
  }

  public clear(): void {
    this.tracks.clear()
  }

  private progress(track: TweenTrack, now: number): number {
    return Math.max(0, Math.min(1, (now - track.start) / TREE_TWEEN_MS))
  }
}

type DynamicRuntime = Pick<GameTreeRuntimeApi, 'suspend' | 'resume'>
type DynamicObjectBuilder = (
  snapshot: TreeRenderSnapshot,
  tree: RenderTree,
) => THREE.Group

export class DynamicTreeObjects {
  private readonly tracks = new TreeTweenTracks()
  private readonly targets = new Map<string, RenderTree>()
  private readonly groups = new Map<string, THREE.Group>()

  public constructor(
    private readonly parent: THREE.Group,
    private readonly runtime: DynamicRuntime,
    private readonly buildObject: DynamicObjectBuilder,
    private readonly releaseObject: (object: THREE.Group) => void = disposeTreeObject,
  ) {}

  public begin(
    tree: RenderTree,
    before: TreeRenderSnapshot,
    after: TreeRenderSnapshot,
    now: number,
  ): void {
    const wasActive = this.tracks.has(tree.id)
    this.tracks.begin(tree.id, before, after, now)
    this.targets.set(tree.id, tree)
    if (!wasActive) this.runtime.suspend(tree.id)
    this.replace(tree.id, this.tracks.at(now).get(tree.id)!, tree)
  }

  public update(now: number): void {
    const completed = this.tracks.takeCompleted(now)
    for (const treeId of completed.keys()) {
      this.remove(treeId)
      const target = this.targets.get(treeId)
      if (target === undefined) throw new Error(`missing dynamic target for tree '${treeId}'`)
      this.targets.delete(treeId)
      this.runtime.resume(target)
    }

    for (const [treeId, snapshot] of this.tracks.at(now)) {
      const target = this.targets.get(treeId)
      if (target === undefined) throw new Error(`missing dynamic target for tree '${treeId}'`)
      this.replace(treeId, snapshot, target)
    }
  }

  public objects(treeId?: string): readonly THREE.Group[] {
    if (treeId !== undefined) {
      const group = this.groups.get(treeId)
      return group === undefined ? [] : [group]
    }
    return [...this.groups.values()]
  }

  public dispose(): void {
    for (const treeId of [...this.groups.keys()]) this.remove(treeId)
    this.targets.clear()
    this.tracks.clear()
  }

  private replace(treeId: string, snapshot: TreeRenderSnapshot, target: RenderTree): void {
    this.remove(treeId)
    const group = this.buildObject(snapshot, target)
    group.userData['treeId'] = treeId
    this.groups.set(treeId, group)
    this.parent.add(group)
  }

  private remove(treeId: string): void {
    const group = this.groups.get(treeId)
    if (group === undefined) return
    this.groups.delete(treeId)
    group.removeFromParent()
    this.releaseObject(group)
  }
}
