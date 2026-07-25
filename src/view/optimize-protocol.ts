import type { Diagram, WireId } from '../kernel/diagram/diagram'
import type { StoredFrame } from './engine'
import type { LayoutBest } from './optimize'

/**
 * Message protocol between the app thread and the layout-search worker
 * (USER ruling 2026-07-24: whole-layout optimization runs ASYNCHRONOUSLY —
 * the user perceives nothing of the search; frames only approach the best
 * known). Everything crossing the boundary is structured-clone data: the
 * kernel Diagram is plain records, poses/nets are Maps of plain objects.
 *
 * Flow control: the client sends at most one `sync` in flight; the worker
 * acks with `synced` and the client then sends the newest pending state
 * (coalescing — a drag streams pin poses without flooding the worker).
 */

export type LayoutPoses = ReadonlyMap<string, { pos: { x: number; y: number }; theta: number }>
export type LayoutNets = ReadonlyMap<string, { junctions: { x: number; y: number }[]; edges: [number, number][] }>

export type SyncMsg = {
  readonly type: 'sync'
  readonly seq: number
  /** bumped when the diagram identity changes; carries the diagram then */
  readonly scene: number
  readonly diagram: Diagram | null
  readonly boundary: readonly WireId[] | null
  readonly frame: StoredFrame | null
  readonly scale: number
  readonly slotShift: number
  readonly poses: LayoutPoses
  readonly nets: LayoutNets
  readonly pins: readonly string[]
}

export type AdoptMsg = {
  readonly type: 'adopt'
  readonly score: number
  readonly poses: LayoutPoses
  readonly nets: LayoutNets
}

export type ClientMsg = SyncMsg | AdoptMsg

export type BestMsg = {
  readonly type: 'best'
  /** the scene this best belongs to — the client drops stale-scene bests */
  readonly scene: number
  readonly score: number
  readonly poses: LayoutBest['poses']
  readonly nets: LayoutBest['nets']
}

export type SyncedMsg = { readonly type: 'synced'; readonly seq: number }

export type StatusMsg = {
  readonly type: 'status'
  readonly scene: number
  readonly searching: boolean
  /** current annealing temperature (surfaced through the client's debugState). */
  readonly temperature: number
}

export type WorkerMsg = BestMsg | SyncedMsg | StatusMsg
