import type { Engine } from './engine'
import { mkEngine, routeObstacles, routeBounds, wireTerminalPoints } from './engine'
import { settleStep, contentEnergy, wireEnergy, recomputeRegions, resolveOverlaps } from './relax'
import { mkFreeSpace } from './route/freespace'
import { netLength, type WireNet } from './route/network'
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
  // wireEnergy = coarse Euclidean + standoffs; replace its Euclidean part with
  // the routed length by adding the routed/removing nothing — the coarse term
  // is a lower bound of the routed one, so score = routed + (standoffs) +
  // content. Standoffs are inside wireEnergy; subtract the coarse length by
  // computing it directly:
  let coarse = 0
  for (const [, w] of e.wires) {
    const terms = wireTerminalPoints(e, w)
    const pos = (v: number): Vec2 => (v < terms.length ? terms[v]! : w.net.junctions[v - terms.length]!)
    for (const [u, v] of w.net.edges) {
      const a = pos(u), b = pos(v)
      coarse += Math.hypot(a.x - b.x, a.y - b.y)
    }
  }
  return L + (wireEnergy(e) - coarse) + contentEnergy(e)
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
    const trials = bodies.length * DIRS * RADII.length
    while (performance.now() - t0 < budgetMs) {
      if (this.#trialStep === -1) {
        if (this.#cursor >= trials) { this.#exhausted = true; break }
        // set up the next trial: best + one enumerated perturbation
        const bi = Math.floor(this.#cursor / (DIRS * RADII.length))
        const rest = this.#cursor % (DIRS * RADII.length)
        const di = Math.floor(rest / RADII.length)
        const ri = rest % RADII.length
        const id = bodies[bi]!
        applySnapshot(scratch, best)
        const b = scratch.bodies.get(id)!
        if (pinned !== null && pinned.has(id)) { this.#cursor++; continue }
        const r = RADII[ri]! * (b.discR + 2) * scratch.scale
        const a = (2 * Math.PI * di) / DIRS
        b.pos = { x: b.pos.x + r * Math.cos(a), y: b.pos.y + r * Math.sin(a) }
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
