import type { Engine } from './engine'
import { mkEngine, routeObstacles, routeBounds, wireTerminalPoints } from './engine'
import { settleStep, contentEnergy, standoffEnergy, segSeparationE, recomputeRegions, resolveOverlaps } from './relax'
import { mkFreeSpace } from './route/freespace'
import { netLength, netPaths, type WireNet } from './route/network'
import type { Vec2 } from './vec'

/**
 * WHOLE-LAYOUT GLOBAL OPTIMIZATION (USER ruling 2026-07-24): the system seeks
 * a GLOBAL optimum of the entire layout, asynchronously; only the best layout
 * found so far is stored; each frame the visible layout approaches the best
 * known. This supersedes rest-at-the-first-local-minimum for the visible
 * layout — the presentation still moves boundedly per frame, but toward the
 * best found, not merely downhill.
 *
 * The searcher is DETERMINISTIC: a budgeted basin-hopping pass on a SCRATCH
 * engine (never the visible one) with an enumerated perturbation schedule —
 * body index × direction × radius, round-robin — each trial locally settled
 * and scored; strictly better full-layout scores replace the best. The
 * schedule exhausting without improvement puts the searcher to sleep until
 * the boundary changes (diagram identity, pin poses).
 */

/** The one full-layout score: ROUTED wire length + content + standoffs
    (`wireEnergy` is the coarse Euclidean pressure; the score routes). */
export function layoutScore(e: Engine): number {
  const fs = mkFreeSpace(routeObstacles(e), routeBounds(e))
  let L = 0
  for (const [, w] of e.wires) {
    const terms = wireTerminalPoints(e, w)
    if (terms.length < 2) continue
    L += netLength(w.net, terms, fs)
  }
  // routed inter-wire separation: crossings and co-routes are part of the
  // GLOBAL score, so the searcher prefers uncrossed layouts of equal length
  const routedSegs: { wid: string; a: Vec2; b: Vec2 }[] = []
  for (const [wid, w] of e.wires) {
    const terms = wireTerminalPoints(e, w)
    if (terms.length < 2) continue
    for (const { pts } of netPaths(w.net, terms, fs)) {
      for (let i = 0; i + 1 < pts.length; i++) routedSegs.push({ wid, a: pts[i]!, b: pts[i + 1]! })
    }
  }
  return L + standoffEnergy(e) + segSeparationE(routedSegs, e.scale) + contentEnergy(e)
}

export type LayoutBest = {
  readonly score: number
  readonly poses: ReadonlyMap<string, { pos: Vec2; theta: number }>
  readonly nets: ReadonlyMap<string, WireNet>
}

const snapshot = (e: Engine, score: number): LayoutBest => ({
  score,
  poses: new Map([...e.bodies].map(([id, b]) => [id, { pos: { ...b.pos }, theta: b.theta }])),
  nets: new Map([...e.wires].map(([wid, w]) => [wid, {
    junctions: w.net.junctions.map((p) => ({ ...p })),
    edges: w.net.edges.map(([u, v]) => [u, v] as const),
  }])),
})

const applySnapshot = (e: Engine, s: LayoutBest): void => {
  for (const [id, b] of e.bodies) {
    const p = s.poses.get(id)
    if (p !== undefined) { b.pos = { ...p.pos }; b.theta = p.theta }
  }
  for (const [wid, w] of e.wires) {
    const n = s.nets.get(wid)
    if (n !== undefined) {
      w.net.junctions = n.junctions.map((p) => ({ ...p }))
      w.net.edges = n.edges.map(([u, v]) => [u, v])
    }
  }
}

/** Perturbation directions (enumerated — the schedule is deterministic). */
const DIRS = 8
const RADII = [1.0, 2.5]
/** settle steps per trial: enough for the perturbed layout to genuinely
    re-settle into its basin — an unsettled trial scores worse than any rest
    and the search learns nothing (measured with 10: zero improvements ever). */
const TRIAL_STEPS = 200

export class LayoutOptimizer {
  #scratch: Engine | null = null
  #diagram: unknown = null
  #best: LayoutBest | null = null
  #pinsKey = ''
  /** schedule cursor: trial = (body, dir, radius); state machine across ticks */
  #cursor = 0
  #trialStep = -1 // -1: no trial in flight; ≥0: settling step of the current trial
  #exhausted = false

  /** Re-seed against the live engine: diagram change or pin-pose change
      invalidates the stored best (it was scored under other constraints). */
  sync(e: Engine, pinned: ReadonlySet<string> | null): void {
    const pinsKey = pinned === null ? '' : [...pinned].sort().map((id) => {
      const b = e.bodies.get(id)
      return b === undefined ? id : `${id}@${b.pos.x},${b.pos.y}`
    }).join('|')
    if (this.#diagram !== e.d) {
      this.#scratch = mkEngine(e.d, [...e.boundary])
      this.#scratch.frame = e.frame
      this.#scratch.scale = e.scale
      this.#scratch.slotShift = e.slotShift
      this.#diagram = e.d
      this.#best = null
    }
    if (pinsKey !== this.#pinsKey) { this.#best = null; this.#pinsKey = pinsKey }
    if (this.#best === null) {
      // seed the best from the LIVE layout
      const live = snapshot(e, 0)
      applySnapshot(this.#scratch!, live)
      this.#best = snapshot(this.#scratch!, layoutScore(this.#scratch!))
      this.#cursor = 0
      this.#trialStep = -1
      this.#exhausted = false
    }
  }

  best(): LayoutBest | null { return this.#best }

  /** The live layout descended below the stored best: it IS the new best. */
  adoptLive(e: Engine, score: number): void {
    this.#best = snapshot(e, score)
    this.#cursor = 0
    this.#trialStep = -1
    this.#exhausted = false
  }
  get exhausted(): boolean { return this.#exhausted }

  /** One budgeted slice of asynchronous search. Deterministic; returns whether
      the best improved this slice. */
  tick(pinned: ReadonlySet<string> | null, budgetMs: number): boolean {
    const scratch = this.#scratch
    const best = this.#best
    if (scratch === null || best === null || this.#exhausted) return false
    const t0 = performance.now()
    let improved = false
    const bodies = [...scratch.bodies.keys()]
    const singles = bodies.length * DIRS * RADII.length
    const pairs: [number, number][] = []
    for (let i = 0; i < bodies.length; i++) for (let j = i + 1; j < bodies.length; j++) pairs.push([i, j])
    const trials = singles + pairs.length
    while (performance.now() - t0 < budgetMs) {
      if (this.#trialStep === -1) {
        if (this.#cursor >= trials) { this.#exhausted = true; break }
        applySnapshot(scratch, best)
        if (this.#cursor < singles) {
          // single-body hop: best + one enumerated displacement
          const bi = Math.floor(this.#cursor / (DIRS * RADII.length))
          const rest = this.#cursor % (DIRS * RADII.length)
          const di = Math.floor(rest / RADII.length)
          const ri = rest % RADII.length
          const id = bodies[bi]!
          const b = scratch.bodies.get(id)!
          if (pinned !== null && pinned.has(id)) { this.#cursor++; continue }
          const r = RADII[ri]! * (b.discR + 2) * scratch.scale
          const a = (2 * Math.PI * di) / DIRS
          b.pos = { x: b.pos.x + r * Math.cos(a), y: b.pos.y + r * Math.sin(a) }
        } else {
          // PAIR SWAP: exchange two bodies' poses (the coordinated move that
          // uncrosses wires — unreachable by any single-body hop or local step)
          const [i, j] = pairs[this.#cursor - singles]!
          const idA = bodies[i]!, idB = bodies[j]!
          if (pinned !== null && (pinned.has(idA) || pinned.has(idB))) { this.#cursor++; continue }
          const A = scratch.bodies.get(idA)!, B = scratch.bodies.get(idB)!
          const t = { pos: A.pos, theta: A.theta }
          A.pos = B.pos; A.theta = B.theta
          B.pos = t.pos; B.theta = t.theta
        }
        recomputeRegions(scratch)
        resolveOverlaps(scratch)
        this.#trialStep = 0
      } else if (this.#trialStep < TRIAL_STEPS) {
        if (!settleStep(scratch, pinned)) this.#trialStep = TRIAL_STEPS
        else this.#trialStep++
      } else {
        // score the settled trial
        const score = layoutScore(scratch)
        if (score < best.score - 1e-9 * (Math.abs(best.score) + 1)) {
          this.#best = snapshot(scratch, score)
          this.#cursor = 0 // a new basin: restart the schedule around it
          improved = true
        } else {
          this.#cursor++
        }
        this.#trialStep = -1
        if (improved) break
      }
    }
    return improved
  }
}
