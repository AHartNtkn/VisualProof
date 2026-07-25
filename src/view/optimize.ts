import type { RegionId } from '../kernel/diagram/diagram'
import type { BodyKind, Engine } from './engine'
import { mkEngine, subtreeCarriers, frameBounds } from './engine'
import {
  settleStep, contentEnergy, wireEnergy, recomputeRegions, resolveOverlaps, establishFrame,
} from './relax'
import { mkScoreState, applyMove } from './score-delta'
import type { ScoreState } from './score-delta'
import type { WireNet } from './route/network'
import type { Vec2 } from './vec'

/**
 * WHOLE-LAYOUT GLOBAL OPTIMIZATION (USER ruling 2026-07-24): the system seeks
 * a GLOBAL optimum of the entire layout, asynchronously; only the best layout
 * found so far is stored; each frame the visible layout approaches the best
 * known. The searcher is SEEDED SIMULATED ANNEALING (plan Task 4), replacing
 * the old enumerated single-body-hop + pair-swap schedule that exhausted and
 * slept. That schedule had no move expressing a coordinated SUBTREE
 * displacement, so a free cut wedged between two wired nodes was never moved
 * aside (measured: the enumerated searcher cannot improve that trap at all).
 *
 * The annealer runs on a SCRATCH engine (never the visible one). It proposes
 * hierarchical moves (single body, rotation, body swap, rigid subtree shift,
 * sibling-subtree swap) from a seeded xorshift128 stream — NO Math.random, NO
 * Date.now, every move exactly undoable — and accepts by the Metropolis rule
 * against the EXACT incremental energy delta (score-delta.ts). One persistent
 * `ScoreState` is kept alive across the whole annealing chain (built once,
 * committed on accept, aborted on reject); it is rebuilt only on a
 * restart/reseed and after each polish (the local solver moves bodies outside
 * the delta's bookkeeping). After each epoch a local settle POLISHES the
 * scratch to a rest state; only a polished rest state that strictly beats the
 * best is published (the frame approach must only adopt rest states). There is
 * NO exhaustion state: after 8 fruitless reheats the searcher drops to a low
 * duty (one epoch per few seconds) but never claims optimality.
 */

/** The one full-layout score: THE wire energy (soft routed cost + turning +
    separation — relax.wireEnergy) plus content. Nothing else exists. */
export function layoutScore(e: Engine): number {
  return wireEnergy(e) + contentEnergy(e)
}

export type LayoutBest = {
  readonly score: number
  readonly poses: ReadonlyMap<string, { pos: Vec2; theta: number }>
  readonly nets: ReadonlyMap<string, WireNet>
}

export const layoutSnapshot = (e: Engine, score: number): LayoutBest => ({
  score,
  poses: new Map([...e.bodies].map(([id, b]) => [id, { pos: { ...b.pos }, theta: b.theta }])),
  nets: new Map([...e.wires].map(([wid, w]) => [wid, {
    junctions: w.net.junctions.map((p) => ({ ...p })),
    edges: w.net.edges.map(([u, v]) => [u, v] as const),
  }])),
})

export const applyLayoutSnapshot = (e: Engine, s: LayoutBest): void => {
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

// ---- seeded PRNG (xorshift128, Marsaglia) — deterministic; NO Math.random ----

export type Rng = () => number

/** A seeded xorshift128 generator returning floats in [0, 1). One number seeds
    the four state words (non-zero by construction). Deterministic and
    reproducible — the whole search path is a pure function of the seed. */
export function mkRng(seed: number): Rng {
  let x = seed >>> 0
  if (x === 0) x = 0x9e3779b9
  let y = (0x243f6a88 ^ x) >>> 0, z = 0xb7e15162, w = 0x9e3779b9
  return () => {
    const t = (x ^ ((x << 11) >>> 0)) >>> 0
    x = y; y = z; z = w
    w = (w ^ (w >>> 19) ^ (t ^ (t >>> 8))) >>> 0
    return w / 0x100000000
  }
}

// ---- the movable-unit taxonomy and the move registry -----------------------

/** A unit of layout state a move can act on. The coverage test enumerates these
    FROM an engine and asserts every one is covered by some registered move —
    adding a unit kind without a mover must fail that test. */
export type MovableUnit =
  | { readonly kind: 'body'; readonly bodyKind: BodyKind; readonly id: string }
  | { readonly kind: 'region'; readonly id: RegionId }
  | { readonly kind: 'endDot'; readonly id: string }

/** Every movable unit of an engine: each body (by kind), each region subtree
    (via childrenOf), and each wire-owned end dot (via endBodyId). */
export function movableUnits(e: Engine): MovableUnit[] {
  const units: MovableUnit[] = []
  for (const [id, b] of e.bodies) units.push({ kind: 'body', bodyKind: b.kind, id })
  for (const rid of e.childrenOf.keys()) units.push({ kind: 'region', id: rid })
  for (const [, w] of e.wires) if (w.endBodyId !== null) units.push({ kind: 'endDot', id: w.endBodyId })
  return units
}

/** A tentative move: the ids whose pose it changed and its exact undo (restore
    the saved poses). Every move is exactly reversible so a rejected Metropolis
    trial leaves the scratch bit-identical. */
type Proposal = { readonly moved: Set<string>; undo(): void }

export type MoveKind = {
  readonly name: string
  /** Does this move act on the given unit? (coverage predicate, data only.) */
  covers(u: MovableUnit): boolean
  /** Is at least one valid (non-pinned) target of this kind present? */
  applicable(e: Engine, pinned: ReadonlySet<string>): boolean
  /** Mutate the engine with one seeded move and return its undo, or null if no
      target is available (applicable() false). */
  propose(e: Engine, pinned: ReadonlySet<string>, rng: Rng): Proposal | null
}

/** Octave ladder for displacement magnitude (plan Task 4): {½, 1, 2, 4}× the
    base clearance. Four octaves because the largest useful displacement is
    bounded by the frame half-extent (~8 disc radii) and the smallest is a
    disc-clearing local jitter; a uniform draw over the octaves is the
    no-information prior over hop scales (NOT a tuned mix). */
const OCTAVES = [0.5, 1, 2, 4] as const
const octaveBase = (rng: Rng): number => OCTAVES[Math.floor(rng() * OCTAVES.length)]!

const isPortBearing = (kind: BodyKind): boolean =>
  kind === 'ref' || kind === 'term' || kind === 'atom' || kind === 'body'

/** Save the exact pose of a body set; the returned thunk restores it. */
function savePoses(e: Engine, ids: Iterable<string>): () => void {
  const saved: { id: string; pos: Vec2; theta: number }[] = []
  for (const id of ids) { const b = e.bodies.get(id)!; saved.push({ id, pos: { ...b.pos }, theta: b.theta }) }
  return () => { for (const s of saved) { const b = e.bodies.get(s.id)!; b.pos = { ...s.pos }; b.theta = s.theta } }
}

const nonPinnedIds = (e: Engine, pinned: ReadonlySet<string>): string[] => {
  const out: string[] = []
  for (const id of e.bodies.keys()) if (!pinned.has(id)) out.push(id)
  return out
}
const portBearingIds = (e: Engine, pinned: ReadonlySet<string>): string[] => {
  const out: string[] = []
  for (const [id, b] of e.bodies) if (!pinned.has(id) && isPortBearing(b.kind)) out.push(id)
  return out
}
const subtreeHasPinned = (e: Engine, rid: RegionId, pinned: ReadonlySet<string>): boolean => {
  if (pinned.size === 0) return false
  for (const id of subtreeCarriers(e, rid)) if (pinned.has(id)) return true
  return false
}
/** Regions whose entire subtree is free of pinned bodies (a subtree move
    containing a pinned body is skipped — pinned bodies never move). */
const movableRegionIds = (e: Engine, pinned: ReadonlySet<string>): RegionId[] => {
  const out: RegionId[] = []
  for (const rid of e.childrenOf.keys()) if (!subtreeHasPinned(e, rid, pinned)) out.push(rid)
  return out
}
/** Groups of ≥2 sibling regions each with a pinned-free subtree (swap targets). */
const siblingGroups = (e: Engine, pinned: ReadonlySet<string>): RegionId[][] => {
  const groups: RegionId[][] = []
  for (const [, kids] of e.childrenOf) {
    const elig = kids.filter((c) => !subtreeHasPinned(e, c, pinned))
    if (elig.length >= 2) groups.push(elig)
  }
  return groups
}
/** Two distinct uniform indices in [0, n) (n ≥ 2), drawn in a fixed order. */
const twoDistinct = (rng: Rng, n: number): [number, number] => {
  const i = Math.floor(rng() * n)
  let j = Math.floor(rng() * (n - 1))
  if (j >= i) j++
  return [i, j]
}

/** The move registry — DATA the annealer proposes from and the coverage test
    checks. Displacement covers every body and end dot; subtree moves cover
    every region; rotation covers port-bearing bodies; body/subtree swaps add
    coordinated exchanges no single-body move can express. */
export const MOVE_REGISTRY: readonly MoveKind[] = [
  {
    name: 'displaceBody',
    covers: (u) => u.kind === 'body' || u.kind === 'endDot',
    applicable: (e, pinned) => nonPinnedIds(e, pinned).length >= 1,
    propose: (e, pinned, rng) => {
      const ids = nonPinnedIds(e, pinned)
      if (ids.length === 0) return null
      const id = ids[Math.floor(rng() * ids.length)]!
      const b = e.bodies.get(id)!
      const undo = savePoses(e, [id])
      const r = octaveBase(rng) * (b.discR + 2) * e.scale
      const a = rng() * 2 * Math.PI
      b.pos = { x: b.pos.x + Math.cos(a) * r, y: b.pos.y + Math.sin(a) * r }
      return { moved: new Set([id]), undo }
    },
  },
  {
    name: 'rotateBody',
    covers: (u) => u.kind === 'body' && isPortBearing(u.bodyKind),
    applicable: (e, pinned) => portBearingIds(e, pinned).length >= 1,
    propose: (e, pinned, rng) => {
      const ids = portBearingIds(e, pinned)
      if (ids.length === 0) return null
      const id = ids[Math.floor(rng() * ids.length)]!
      const b = e.bodies.get(id)!
      const undo = savePoses(e, [id])
      b.theta += (rng() * 2 - 1) * Math.PI
      return { moved: new Set([id]), undo }
    },
  },
  {
    name: 'swapBodies',
    covers: (u) => u.kind === 'body' || u.kind === 'endDot',
    applicable: (e, pinned) => nonPinnedIds(e, pinned).length >= 2,
    propose: (e, pinned, rng) => {
      const ids = nonPinnedIds(e, pinned)
      if (ids.length < 2) return null
      const [i, j] = twoDistinct(rng, ids.length)
      const a = e.bodies.get(ids[i]!)!, b = e.bodies.get(ids[j]!)!
      const undo = savePoses(e, [ids[i]!, ids[j]!])
      const ap = a.pos, at = a.theta
      a.pos = b.pos; a.theta = b.theta
      b.pos = ap; b.theta = at
      return { moved: new Set([ids[i]!, ids[j]!]), undo }
    },
  },
  {
    name: 'displaceSubtree',
    covers: (u) => u.kind === 'region',
    applicable: (e, pinned) => movableRegionIds(e, pinned).length >= 1,
    propose: (e, pinned, rng) => {
      const rids = movableRegionIds(e, pinned)
      if (rids.length === 0) return null
      const rid = rids[Math.floor(rng() * rids.length)]!
      const carriers = subtreeCarriers(e, rid)
      const undo = savePoses(e, carriers)
      const radius = e.regions.get(rid)?.radius ?? 10 * e.scale
      const r = octaveBase(rng) * radius
      const a = rng() * 2 * Math.PI
      const dx = Math.cos(a) * r, dy = Math.sin(a) * r
      for (const c of carriers) { const b = e.bodies.get(c)!; b.pos = { x: b.pos.x + dx, y: b.pos.y + dy } }
      return { moved: new Set(carriers), undo }
    },
  },
  {
    name: 'swapSubtrees',
    covers: (u) => u.kind === 'region',
    applicable: (e, pinned) => siblingGroups(e, pinned).length >= 1,
    propose: (e, pinned, rng) => {
      const groups = siblingGroups(e, pinned)
      if (groups.length === 0) return null
      const g = groups[Math.floor(rng() * groups.length)]!
      const [i, j] = twoDistinct(rng, g.length)
      const r1 = g[i]!, r2 = g[j]!
      const c1 = e.regions.get(r1)!.center, c2 = e.regions.get(r2)!.center
      const dx = c2.x - c1.x, dy = c2.y - c1.y
      const car1 = subtreeCarriers(e, r1), car2 = subtreeCarriers(e, r2)
      const undo = savePoses(e, [...car1, ...car2])
      for (const c of car1) { const b = e.bodies.get(c)!; b.pos = { x: b.pos.x + dx, y: b.pos.y + dy } }
      for (const c of car2) { const b = e.bodies.get(c)!; b.pos = { x: b.pos.x - dx, y: b.pos.y - dy } }
      return { moved: new Set([...car1, ...car2]), undo }
    },
  },
]

// ---- the annealer ----------------------------------------------------------

/** Default module seed for the worker's optimizer (tests pass explicit seeds). */
const DEFAULT_SEED = 0x1234abcd
/** Probe batch for temperature calibration: T0 is the TYPICAL-move |dE| over
    this many seeded moves at the seed state, giving a typical move an initial
    acceptance of ~e^-1 (the brief's stated calibration goal). 64 makes the
    statistic stable. The typical-move scale is the MEDIAN, not the mean: under
    the uncapped sibling barrier (plan 23) an occasional move flings a body into
    deep overlap or out of the frame, so |dE| is heavy-tailed (measured on the
    acceptance fixture: median 1500, mean 3.5e6 — three decades apart). The mean
    is set by that tail and makes T0 so high that every move is accepted (a
    random walk, not annealing); the median IS the typical move and makes
    exp(-|dE|/T0) ≈ e^-1 for it while the catastrophic tail is rejected — which
    is precisely the e^-1 goal the "mean" wording was a proxy for. */
const PROBE_BATCH = 64
/** Per-epoch geometric cooling: T ← 0.95·T. Slow enough that each temperature
    sees meaningful acceptance statistics before the next. */
const COOL = 0.95
/** Proposals per movable DOF per temperature (epoch = 8·(bodies+regions)): the
    smallest multiple giving acceptance statistics meaning. */
const EPOCH_PER_DOF = 8
/** Reheat floor: reheat once T falls below T0/1000 — the score's measured
    dynamic range is ~3 decades, so below this no proposal is ever accepted. */
const REHEAT_FLOOR = 1 / 1000
/** Consecutive fruitless reheats before dropping to low duty. 8 covers both
    restart flavors (best-perturb / fresh) four times each. */
const LOW_DUTY_REHEATS = 8
/** Polish settles the scratch TO REST every epoch (the brief publishes only
    rest states), looping settleStep until it reports rest. This cap bounds
    per-epoch latency: a GOOD candidate settles in a few hundred steps (measured
    758 on the acceptance escape), while an anneal epoch that scattered badly can
    take thousands and is not a candidate worth publishing anyway — so polish
    abandons it here and the epoch stays cheap. Any value comfortably above a
    good candidate's steps-to-rest gives the same set of published bests; it
    caps wasted work on non-converging scatters, it is not a quality knob. A
    wall-clock cap is rejected: it would make the published-best sequence
    machine-dependent and break the determinism contract. */
const POLISH_REST_CAP = 2000

const eps = (x: number): number => 1e-9 * (Math.abs(x) + 1)
const EMPTY: ReadonlySet<string> = new Set()

export class LayoutOptimizer {
  readonly #seed: number
  #rng: Rng
  #scratch: Engine | null = null
  #st: ScoreState | null = null
  #best: LayoutBest | null = null
  #diagram: unknown = null
  #pinsKey = ''
  #pinned: ReadonlySet<string> = EMPTY
  #pinnedPoses = new Map<string, { pos: Vec2; theta: number }>()
  #T = 0
  #T0 = 0
  /** alternates best-perturb (even) / fresh-arrangement (odd) restarts */
  #restartParity = 0
  #reheatsSinceImprove = 0
  #lowDuty = false

  constructor(seed: number = DEFAULT_SEED) {
    this.#seed = (seed >>> 0) || DEFAULT_SEED
    this.#rng = mkRng(this.#seed)
  }

  /** Re-seed against the live engine: a diagram change or pin-pose change
      invalidates the stored best (it was scored under other constraints). */
  sync(e: Engine, pinned: ReadonlySet<string> | null): void {
    this.#pinned = pinned === null ? EMPTY : new Set(pinned)
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
    if (this.#best === null) this.#reseedFrom(e)
  }

  best(): LayoutBest | null { return this.#best }

  /** Always searching — simulated annealing never exhausts. */
  get searching(): boolean { return true }
  /** In low duty: the worker spaces epochs a few seconds apart (still searching). */
  get lowDuty(): boolean { return this.#lowDuty }
  /** Current annealing temperature (for the status debug seam). */
  get temperature(): number { return this.#T }

  /** The live layout is strictly better than the stored best — adopt it. */
  adoptLive(e: Engine, score: number): void {
    this.#best = layoutSnapshot(e, score)
    this.#reheatsSinceImprove = 0
    this.#lowDuty = false
  }

  /** One budgeted slice of asynchronous search. Runs whole epochs until the
      wall budget is spent (always at least one), or exactly one epoch in low
      duty. Returns whether the published best improved this slice. */
  tick(_pinned: ReadonlySet<string> | null, budgetMs: number): boolean {
    if (this.#scratch === null || this.#best === null || this.#st === null) return false
    const t0 = performance.now()
    let improved = false
    do {
      if (this.#runEpoch()) improved = true
    } while (!this.#lowDuty && performance.now() - t0 < budgetMs)
    return improved
  }

  // -- internals --

  #reseedFrom(e: Engine): void {
    const scratch = this.#scratch!
    applyLayoutSnapshot(scratch, layoutSnapshot(e, 0))
    recomputeRegions(scratch)
    if (scratch.frame === null) establishFrame(scratch)
    this.#pinnedPoses = new Map()
    for (const id of this.#pinned) {
      const b = scratch.bodies.get(id)
      if (b !== undefined) this.#pinnedPoses.set(id, { pos: { ...b.pos }, theta: b.theta })
    }
    this.#best = layoutSnapshot(scratch, layoutScore(scratch))
    this.#rng = mkRng(this.#seed)
    this.#st = mkScoreState(scratch)
    this.#T0 = this.#calibrateT0()
    this.#T = this.#T0
    this.#restartParity = 0
    this.#reheatsSinceImprove = 0
    this.#lowDuty = false
  }

  /** T0 = the typical (median) |dE| over a seeded probe batch at the seed
      state; the probes abort (they measure, they do not advance the state). */
  #calibrateT0(): number {
    const scratch = this.#scratch!, st = this.#st!, pinned = this.#pinned, rng = this.#rng
    const mags: number[] = []
    for (let k = 0; k < PROBE_BATCH; k++) {
      const kinds = MOVE_REGISTRY.filter((m) => m.applicable(scratch, pinned))
      if (kinds.length === 0) break
      const kind = kinds[Math.floor(rng() * kinds.length)]!
      const p = kind.propose(scratch, pinned, rng)
      if (p === null) continue
      recomputeRegions(scratch)
      const res = applyMove(scratch, st, p.moved)
      mags.push(Math.abs(res.dE))
      p.undo(); recomputeRegions(scratch); res.abort()
    }
    if (mags.length === 0) return 0
    mags.sort((a, b) => a - b)
    return mags[mags.length >> 1]!
  }

  /** The DOF count driving the epoch length and reheat cadence. */
  #dofCount(): number {
    return nonPinnedIds(this.#scratch!, this.#pinned).length + this.#scratch!.childrenOf.size
  }

  #runEpoch(): boolean {
    const E = EPOCH_PER_DOF * this.#dofCount()
    const accepts = this.#annealEpoch(E)
    this.#T *= COOL
    const improved = this.#polish()
    if (this.#T < this.#T0 * REHEAT_FLOOR || accepts === 0) this.#reheat()
    return improved
  }

  /** One epoch of E Metropolis moves at the current (constant) temperature
      against the persistent ScoreState: commit on accept, un-mutate + abort on
      reject. Returns the number accepted. */
  #annealEpoch(E: number): number {
    const scratch = this.#scratch!, st = this.#st!, pinned = this.#pinned, rng = this.#rng
    const T = this.#T
    let accepts = 0
    for (let m = 0; m < E; m++) {
      const kinds = MOVE_REGISTRY.filter((mk) => mk.applicable(scratch, pinned))
      if (kinds.length === 0) break
      const kind = kinds[Math.floor(rng() * kinds.length)]!
      const p = kind.propose(scratch, pinned, rng)
      if (p === null) continue
      recomputeRegions(scratch)
      const res = applyMove(scratch, st, p.moved)
      const dE = res.dE
      const accept = dE < 0 || (T > 0 && rng() < Math.exp(-dE / T))
      if (accept) { res.commit(); accepts++ }
      else { p.undo(); recomputeRegions(scratch); res.abort() }
    }
    return accepts
  }

  /** Local settle on the scratch TO REST (settleStep until it reports no
      motion, bounded by the non-convergence backstop). Only a rest state that
      strictly beats the best is published (the frame approach adopts only rest
      states). Rebuild the tracked ScoreState after — the local solver moved
      bodies outside the delta's bookkeeping. */
  #polish(): boolean {
    const scratch = this.#scratch!, pinned = this.#pinned
    let atRest = false
    for (let s = 0; s < POLISH_REST_CAP; s++) {
      if (!settleStep(scratch, pinned)) { atRest = true; break }
    }
    recomputeRegions(scratch)
    let improved = false
    if (atRest) {
      const score = layoutScore(scratch)
      const best = this.#best!
      if (score < best.score - eps(best.score)) {
        this.#best = layoutSnapshot(scratch, score)
        improved = true
        this.#reheatsSinceImprove = 0
        this.#lowDuty = false
      }
    }
    this.#st = mkScoreState(scratch)
    return improved
  }

  /** Reheat: alternate seeded restarts — (a) the incumbent best (the following
      epoch at T0 is its one-epoch perturbation) and (b) a fresh random
      arrangement. Resets T to T0; after enough fruitless reheats, drops to low
      duty. */
  #reheat(): void {
    this.#reheatsSinceImprove++
    if (this.#reheatsSinceImprove >= LOW_DUTY_REHEATS) this.#lowDuty = true
    const parity = this.#restartParity++ % 2
    if (parity === 0) {
      applyLayoutSnapshot(this.#scratch!, this.#best!)
      recomputeRegions(this.#scratch!)
      this.#restorePinned()
    } else {
      this.#freshArrangement()
    }
    this.#st = mkScoreState(this.#scratch!)
    this.#T = this.#T0
  }

  #restorePinned(): void {
    const scratch = this.#scratch!
    for (const [id, pp] of this.#pinnedPoses) {
      const b = scratch.bodies.get(id)
      if (b !== undefined) { b.pos = { ...pp.pos }; b.theta = pp.theta }
    }
  }

  /** A fresh random arrangement: bodies placed by seeded uniform draws inside
      the frame (pinned bodies kept), nets reseeded as in mkEngine, then the
      construction-time overlap projection. */
  #freshArrangement(): void {
    const prev = this.#scratch!
    const g = mkEngine(prev.d, [...prev.boundary])
    g.frame = prev.frame; g.scale = prev.scale; g.slotShift = prev.slotShift
    const fb = frameBounds(g)
    const rng = this.#rng
    for (const [id, b] of g.bodies) {
      if (this.#pinned.has(id)) {
        const pp = this.#pinnedPoses.get(id)
        if (pp !== undefined) { b.pos = { ...pp.pos }; b.theta = pp.theta }
        continue
      }
      b.pos = fb === null
        ? { x: (rng() * 2 - 1) * 40, y: (rng() * 2 - 1) * 40 }
        : { x: fb.center.x + (rng() * 2 - 1) * fb.frameR, y: fb.center.y + (rng() * 2 - 1) * fb.frameR }
      b.theta = (rng() * 2 - 1) * Math.PI
    }
    recomputeRegions(g)
    resolveOverlaps(g)
    recomputeRegions(g)
    this.#scratch = g
  }
}
