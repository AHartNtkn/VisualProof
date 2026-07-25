import type { Engine } from './engine'
import type { LayoutSearch } from './relax'
import type { LayoutBest } from './optimize'
import { layoutSnapshot } from './optimize'
import type { ClientMsg, LayoutNets, LayoutPoses, SyncMsg, WorkerMsg } from './optimize-protocol'

/**
 * App-thread adapter for the layout-search worker: implements the
 * LayoutSearch seam the frame polls (see relax.ts). All heavy minimization
 * happens in the worker; this class only serializes live state out and
 * caches best snapshots in. Syncs are ack-coalesced — at most one in
 * flight, the newest pending state sent when the worker acks — so a drag
 * streaming pin poses can never flood the worker.
 */

const posesOf = (e: Engine): LayoutPoses =>
  new Map([...e.bodies].map(([id, b]) => [id, { pos: { ...b.pos }, theta: b.theta }]))

const netsOf = (e: Engine): LayoutNets =>
  new Map([...e.wires].map(([wid, w]) => [wid, {
    junctions: w.net.junctions.map((p) => ({ ...p })),
    edges: w.net.edges.map(([u, v]) => [u, v] as [number, number]),
  }]))

export class WorkerSearch implements LayoutSearch {
  #worker: Worker
  #best: LayoutBest | null = null
  #searching = true
  #temperature = 0
  #scene = 0
  #sceneDiagram: unknown = null
  #seq = 0
  #ackedSeq = 0
  #pending: SyncMsg | null = null
  #lastSyncKey = ''

  constructor() {
    this.#worker = new Worker(new URL('./optimize-worker.ts', import.meta.url), { type: 'module' })
    // a dead searcher must be LOUD: layout search silently stopping is the
    // frozen-layout defect class (no silent failures)
    this.#worker.onerror = (ev) => { console.error('[search] worker error:', ev.message, ev.filename, ev.lineno) }
    this.#worker.onmessageerror = (ev) => { console.error('[search] worker message error:', ev) }
    this.#worker.onmessage = (ev: MessageEvent<WorkerMsg>) => {
      const m = ev.data
      if (m.type === 'best') {
        if (m.scene === this.#scene) this.#best = { score: m.score, poses: m.poses, nets: m.nets }
      } else if (m.type === 'status') {
        if (m.scene === this.#scene) { this.#searching = m.searching; this.#temperature = m.temperature }
      } else {
        this.#ackedSeq = m.seq
        if (this.#pending !== null) {
          const p = this.#pending
          this.#pending = null
          this.#post(p)
        }
      }
    }
  }

  get searching(): boolean {
    return this.#searching || this.#pending !== null || this.#ackedSeq < this.#seq
  }

  #post(m: ClientMsg): void {
    this.#worker.postMessage(m)
  }

  sync(e: Engine, pinned: ReadonlySet<string> | null): void {
    const sceneChanged = this.#sceneDiagram !== e.d
    if (sceneChanged) {
      this.#scene++
      this.#sceneDiagram = e.d
      this.#best = null
    }
    const pinsKey = pinned === null ? '' : [...pinned].sort().map((id) => {
      const b = e.bodies.get(id)
      return b === undefined ? id : `${id}@${b.pos.x},${b.pos.y}`
    }).join('|')
    const syncKey = `${this.#scene}#${pinsKey}`
    if (!sceneChanged && syncKey === this.#lastSyncKey) return
    if (pinsKey !== '' || sceneChanged) this.#best = null
    this.#lastSyncKey = syncKey
    this.#searching = true
    const msg: SyncMsg = {
      type: 'sync',
      seq: ++this.#seq,
      scene: this.#scene,
      diagram: sceneChanged ? e.d : null,
      boundary: sceneChanged ? [...e.boundary] : null,
      frame: e.frame,
      scale: e.scale,
      slotShift: e.slotShift,
      poses: posesOf(e),
      nets: netsOf(e),
      pins: pinned === null ? [] : [...pinned],
    }
    if (this.#ackedSeq < this.#seq - 1) {
      // one sync in flight: coalesce to the newest state — but a pending
      // sync carrying the scene's diagram must not lose it to a later
      // diagram-less sync of the same scene
      const prev = this.#pending
      this.#pending = prev !== null && prev.scene === msg.scene && prev.diagram !== null && msg.diagram === null
        ? { ...msg, diagram: prev.diagram, boundary: prev.boundary }
        : msg
    } else {
      this.#post(msg)
    }
  }

  best(): LayoutBest | null {
    return this.#best
  }

  /** Debug-seam surface: current search state without log spam. */
  debugState(): { scene: number; searching: boolean; bestScore: number | null; temperature: number } {
    return { scene: this.#scene, searching: this.searching, bestScore: this.#best?.score ?? null, temperature: this.#temperature }
  }

  adoptLive(e: Engine, score: number): void {
    this.#best = layoutSnapshot(e, score)
    this.#searching = true
    this.#post({ type: 'adopt', score, poses: posesOf(e), nets: netsOf(e) })
  }

  dispose(): void {
    this.#worker.terminate()
  }
}

/** Construct the worker-backed search, or null where Workers do not exist
    (jsdom tests): engines without a search run the local solvers. */
export function mkWorkerSearch(): WorkerSearch | null {
  if (typeof Worker === 'undefined') return null
  return new WorkerSearch()
}
