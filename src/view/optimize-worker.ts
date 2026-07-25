import type { Engine } from './engine'
import { mkEngine } from './engine'
import { LayoutOptimizer } from './optimize'
import { recomputeRegions } from './relax'
import type { ClientMsg, WorkerMsg } from './optimize-protocol'

/**
 * The layout-search WORKER (USER ruling 2026-07-24: whole-layout global
 * optimization runs asynchronously; only the best layout found is stored;
 * the visible layout approaches it over time). This thread owns ALL heavy
 * minimization: the trial schedule and every scratch settle run here, off
 * the frame thread. It mirrors the live scene from `sync` messages, drives
 * the deterministic LayoutOptimizer in time slices, and posts each strictly
 * better layout back as a `best` snapshot.
 */

const post = (m: WorkerMsg): void => {
  ;(self as unknown as { postMessage(m: WorkerMsg): void }).postMessage(m)
}

/** Per-slice tick budget. The worker yields to its message queue between
    slices so incoming syncs (drags, edits) are never starved. */
const SLICE_MS = 200

let mirror: Engine | null = null
let scene = -1
let opt = new LayoutOptimizer()
let pins: ReadonlySet<string> | null = null
let pumping = false
let lastSearching: boolean | null = null

function applyToMirror(m: Extract<ClientMsg, { type: 'sync' }>): void {
  if (m.scene !== scene) {
    if (m.diagram === null || m.boundary === null) {
      throw new Error(`layout worker: scene ${m.scene} announced without a diagram (client protocol bug)`)
    }
    mirror = mkEngine(m.diagram, [...m.boundary])
    scene = m.scene
    opt = new LayoutOptimizer()
  }
  const e = mirror
  if (e === null) throw new Error('layout worker: sync before any scene')
  e.frame = m.frame
  e.scale = m.scale
  e.slotShift = m.slotShift
  for (const [id, p] of m.poses) {
    const b = e.bodies.get(id)
    if (b !== undefined) { b.pos = { ...p.pos }; b.theta = p.theta }
  }
  for (const [wid, n] of m.nets) {
    const w = e.wires.get(wid)
    if (w !== undefined) {
      w.net.junctions = n.junctions.map((p) => ({ ...p }))
      w.net.edges = n.edges.map(([u, v]) => [u, v])
    }
  }
  recomputeRegions(e)
  pins = m.pins.length === 0 ? null : new Set(m.pins)
}

function publishBest(): void {
  const b = opt.best()
  if (b !== null) post({ type: 'best', scene, score: b.score, poses: b.poses, nets: b.nets })
}

function publishStatus(): void {
  const searching = !opt.exhausted
  if (searching !== lastSearching) {
    lastSearching = searching
    post({ type: 'status', scene, searching })
  }
}

function pump(): void {
  pumping = false
  if (mirror === null || opt.exhausted) { publishStatus(); return }
  // an exception here escapes to the client's worker.onerror and STOPS the
  // pump — a dead search is reported loudly, never rescheduled silently
  const improved = opt.tick(pins, SLICE_MS)
  if (improved) publishBest()
  publishStatus()
  if (!opt.exhausted) schedule()
}

/** Yield-then-continue via a MessageChannel: unlike setTimeout, channel
    messages are NOT throttled in background tabs — the search keeps full
    speed when the app tab is hidden. */
const pumpChannel = new MessageChannel()
pumpChannel.port1.onmessage = () => pump()

function schedule(): void {
  if (pumping) return
  pumping = true
  pumpChannel.port2.postMessage(null)
}

self.onmessage = (ev: MessageEvent<ClientMsg>) => {
  const m = ev.data
  if (m.type === 'sync') {
    applyToMirror(m)
    opt.sync(mirror!, pins)
    post({ type: 'synced', seq: m.seq })
    // a (re)seeded searcher has a best immediately — publish it so the client
    // never approaches a stale snapshot from a previous scene
    publishBest()
    lastSearching = null
    publishStatus()
    schedule()
  } else {
    const e = mirror
    if (e === null) return
    for (const [id, p] of m.poses) {
      const b = e.bodies.get(id)
      if (b !== undefined) { b.pos = { ...p.pos }; b.theta = p.theta }
    }
    for (const [wid, n] of m.nets) {
      const w = e.wires.get(wid)
      if (w !== undefined) {
        w.net.junctions = n.junctions.map((p) => ({ ...p }))
        w.net.edges = n.edges.map(([u, v]) => [u, v])
      }
    }
    recomputeRegions(e)
    opt.adoptLive(e, m.score)
    lastSearching = null
    publishStatus()
    schedule()
  }
}
