import * as THREE from 'three'
import type { scene3 } from '../../view3d/scene'
import { SceneTweenTrack } from '../../view3d/transition'
import type { GameTreeRuntimeApi, RenderTree } from './runtime'
import { disposeTreeObject } from './tree-objects'

export type TreeRenderSnapshot = ReturnType<typeof scene3>

class TreeTweenTracks {
  private readonly tracks = new Map<string, SceneTweenTrack>()

  public prepare(
    treeId: string,
    before: TreeRenderSnapshot,
    after: TreeRenderSnapshot,
    now: number,
  ): SceneTweenTrack {
    const displayed = this.tracks.get(treeId)?.sample(now) ?? before
    return new SceneTweenTrack(displayed, after, now)
  }

  public commit(treeId: string, track: SceneTweenTrack): void {
    this.tracks.set(treeId, track)
  }

  public has(treeId: string): boolean {
    return this.tracks.has(treeId)
  }

  public at(now: number): ReadonlyMap<string, TreeRenderSnapshot> {
    const frames = new Map<string, TreeRenderSnapshot>()
    for (const [treeId, track] of this.tracks) {
      frames.set(treeId, track.sample(now))
    }
    return frames
  }

  public takeCompleted(now: number): ReadonlyMap<string, TreeRenderSnapshot> {
    const completed = new Map<string, TreeRenderSnapshot>()
    for (const [treeId, track] of this.tracks) {
      if (!track.completed(now)) continue
      completed.set(treeId, track.target)
      this.tracks.delete(treeId)
    }
    return completed
  }

  public clear(): void {
    this.tracks.clear()
  }
}

type DynamicRuntime = Pick<GameTreeRuntimeApi, 'suspend' | 'resume'>
type DynamicObjectBuilder = (
  snapshot: TreeRenderSnapshot,
  tree: RenderTree,
) => THREE.Group

type PreparedDynamicTreeUpdate = {
  readonly tree: RenderTree
  readonly track: SceneTweenTrack
  readonly object: THREE.Group
  readonly wasActive: boolean
}

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

  public prepare(
    tree: RenderTree,
    before: TreeRenderSnapshot,
    after: TreeRenderSnapshot,
    now: number,
    buildObject: DynamicObjectBuilder = this.buildObject,
  ): PreparedDynamicTreeUpdate {
    const track = this.tracks.prepare(tree.id, before, after, now)
    return {
      tree,
      track,
      object: buildObject(track.sample(now), tree),
      wasActive: this.tracks.has(tree.id),
    }
  }

  public commit(prepared: PreparedDynamicTreeUpdate): void {
    this.tracks.commit(prepared.tree.id, prepared.track)
    this.targets.set(prepared.tree.id, prepared.tree)
    if (!prepared.wasActive) this.runtime.suspend(prepared.tree.id)
    this.replaceWith(prepared.tree.id, prepared.object)
  }

  public discard(prepared: PreparedDynamicTreeUpdate): void {
    this.releaseObject(prepared.object)
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

  public clear(): void {
    for (const treeId of [...this.groups.keys()]) this.remove(treeId)
    this.targets.clear()
    this.tracks.clear()
  }

  public dispose(): void {
    this.clear()
  }

  private replace(treeId: string, snapshot: TreeRenderSnapshot, target: RenderTree): void {
    const group = this.buildObject(snapshot, target)
    this.replaceWith(treeId, group)
  }

  private replaceWith(treeId: string, group: THREE.Group): void {
    this.remove(treeId)
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
