import type { RegionId, WireId } from '../kernel/diagram/diagram'
import type { BodyKind, Engine, WireView } from './engine'
import { mkEngine, subtreeCarriers, frameBounds, wireTerminalPoints } from './engine'
import {
  settleStep, contentEnergy, wireEnergy, recomputeRegions, resolveOverlaps, establishFrame,
} from './relax'
import type { WireNet } from './route/network'
import { FD_PROBE } from './route/network'
import { mkScoreState, applyMove } from './score-delta'
import type { ScoreState } from './score-delta'
import type { Vec2 } from './vec'

/**
 * WHOLE-LAYOUT GLOBAL OPTIMIZATION (USER rulings 2026-07-24 and 2026-07-31):
 * the system seeks a global optimum asynchronously; only the best layout found
 * so far is stored; each frame the visible layout approaches the best known.
 *
 * THE UNIFIED CHAIN (2026-07-31 spec, user-approved — supersedes basin
 * hopping): the worker runs ONE seeded Metropolis chain over multi-scale
 * moves (single body, rotation, windowed swaps, rigid subtree, junction),
 * every proposal priced by the EXACT incremental delta (score-delta) — no
 * whole-scene evaluations, no quench between moves, no gradient probes. A
 * RANGE FACTOR D scales every move kind's natural amplitude and adapts to
 * the measured acceptance rate by VPR's published rule (target 0.44), so
 * descent emerges as the low-temperature, small-range tail of the same
 * chain that explores at high temperature. The deterministic solver
 * (settleStep) survives as the streamed SEED POLISH and as the REST
 * CERTIFICATE a candidate best passes before publishing — so every
 * published best past the seed's own monotone descent is a certified rest.
 * Seeded xorshift128 throughout (NO Math.random, NO Date.now); after 8
 * fruitless reheats the chain drops to low duty but never claims optimality.
 */

/** The one full-layout score: THE wire energy (soft routed cost + turning +
    separation — relax.wireEnergy) plus content. Nothing else exists. Basin
    hopping scores only relaxed (rest) states, so a cheap full eval suffices —
    no incremental delta is needed or kept. */
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
  | { readonly kind: 'carrier'; readonly carrierKind: BodyKind; readonly id: string }
  | { readonly kind: 'region'; readonly id: RegionId }
  | { readonly kind: 'junction'; readonly wid: WireId; readonly j: number }

/** Every movable unit of an engine: each body (by kind), each region subtree
    (via childrenOf), and each wire junction (a routed Steiner point — a
    positional DOF the local walk can only settle within its basin, so
    crossing a junction cusp is a search-layer move). */
export function movableUnits(e: Engine): MovableUnit[] {
  const units: MovableUnit[] = []
  for (const [id, b] of e.bodies) units.push({ kind: 'carrier', carrierKind: b.kind, id })
  for (const rid of e.childrenOf.keys()) units.push({ kind: 'region', id: rid })
  for (const [wid, w] of e.wires) for (let j = 0; j < w.net.junctions.length; j++) units.push({ kind: 'junction', wid, j })
  return units
}

/** A tentative move: the ids whose pose it changed and its exact undo. Basin
    hopping restores a rejected hop from the whole-basin snapshot (relaxation
    moves more than the move did), so it does not use `undo`; the field is the
    move library's own contract, unchanged from the annealer. */
type Proposal = {
  readonly moved: Set<string>
  /** Wires whose OWN state (junctions) the move changed — forced into the
      delta evaluator's affected set. */
  readonly wids?: ReadonlySet<WireId>
  undo(): void
}

export type MoveKind = {
  readonly name: string
  /** Does this move act on the given unit? (coverage predicate, data only.) */
  covers(u: MovableUnit): boolean
  /** Is at least one valid (non-pinned) target of this kind present? */
  applicable(e: Engine, pinned: ReadonlySet<string>): boolean
  /** Mutate the engine with one seeded move at range factor D ∈ (0, 1] and
      return its undo, or null if no target is available. Displacements are
      D × the kind's natural unit, floored at FD_PROBE (the sensing floor),
      sampled AT that radius (Davidson–Harel perimeter sampling); swaps are
      eligible only within the D-window (VPR's interchange rule). */
  propose(e: Engine, pinned: ReadonlySet<string>, rng: Rng, D: number): Proposal | null
}

/** Range-limited amplitude: D × the move kind's natural unit, floored at the
    sensing floor (a displacement below FD_PROBE is below what any gate can
    resolve from noise). */
const rangeAmp = (D: number, unit: number): number => Math.max(FD_PROBE, D * unit)

/** The wire's bounding-circle radius: the greatest distance from the terminals'
    centroid to any terminal — the wire's own spatial extent. A junction lives
    within its wire's reach, so this is the natural scale for a junction hop (the
    octave ladder over it spans within-wire to just-past-wire jumps). A degenerate
    wire whose terminals coincide floors at one world unit (e.scale) so the hop is
    never zero. */
function wireBoundRadius(e: Engine, w: WireView): number {
  const ts = wireTerminalPoints(e, w)
  if (ts.length === 0) return e.scale
  let cx = 0, cy = 0
  for (const t of ts) { cx += t.x; cy += t.y }
  cx /= ts.length; cy /= ts.length
  let r = 0
  for (const t of ts) r = Math.max(r, Math.hypot(t.x - cx, t.y - cy))
  return Math.max(r, e.scale)
}

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
  for (const [id, body] of e.bodies) {
    if (!pinned.has(id) && body.localAnchor.size > 0) out.push(id)
  }
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
/** The move registry — DATA the search proposes from and the coverage test
    checks. Displacement covers every body; subtree moves cover every region;
    rotation covers port-bearing bodies; body/subtree swaps add coordinated
    exchanges no single-body move can express. */
export const MOVE_REGISTRY: readonly MoveKind[] = [
  {
    name: 'displaceBody',
    covers: (u) => u.kind === 'carrier',
    applicable: (e, pinned) => nonPinnedIds(e, pinned).length >= 1,
    propose: (e, pinned, rng, D) => {
      const ids = nonPinnedIds(e, pinned)
      if (ids.length === 0) return null
      const id = ids[Math.floor(rng() * ids.length)]!
      const b = e.bodies.get(id)!
      const undo = savePoses(e, [id])
      const r = rangeAmp(D, (b.discR + 2) * e.scale)
      const a = rng() * 2 * Math.PI
      b.pos = { x: b.pos.x + Math.cos(a) * r, y: b.pos.y + Math.sin(a) * r }
      return { moved: new Set([id]), undo }
    },
  },
  {
    name: 'rotateBody',
    covers: (u) => u.kind === 'carrier' && u.carrierKind !== 'anchor',
    applicable: (e, pinned) => portBearingIds(e, pinned).length >= 1,
    propose: (e, pinned, rng, D) => {
      const ids = portBearingIds(e, pinned)
      if (ids.length === 0) return null
      const id = ids[Math.floor(rng() * ids.length)]!
      const b = e.bodies.get(id)!
      const undo = savePoses(e, [id])
      const m = Math.max(b.discR * e.scale, 1e-6)
      b.theta += (rng() < 0.5 ? 1 : -1) * Math.max(FD_PROBE / m, D * Math.PI)
      return { moved: new Set([id]), undo }
    },
  },
  {
    name: 'swapBodies',
    covers: (u) => u.kind === 'carrier',
    applicable: (e, pinned) => nonPinnedIds(e, pinned).length >= 2,
    propose: (e, pinned, rng, D) => {
      const ids = nonPinnedIds(e, pinned)
      if (ids.length < 2) return null
      const i = Math.floor(rng() * ids.length)
      const a = e.bodies.get(ids[i]!)!
      // VPR interchange rule: swap only within the D-window; the floor is the
      // pair's own span so adjacent swaps stay possible at any range
      const win = (other: { pos: Vec2; discR: number }): number =>
        Math.max((a.discR + other.discR + 4) * e.scale, D * 4 * frameHalf(e))
      const near = ids.filter((oid, k) => {
        if (k === i) return false
        const o = e.bodies.get(oid)!
        return Math.hypot(o.pos.x - a.pos.x, o.pos.y - a.pos.y) <= win(o)
      })
      if (near.length === 0) return null
      const jid = near[Math.floor(rng() * near.length)]!
      const b = e.bodies.get(jid)!
      const undo = savePoses(e, [ids[i]!, jid])
      const ap = a.pos, at = a.theta
      a.pos = b.pos; a.theta = b.theta
      b.pos = ap; b.theta = at
      return { moved: new Set([ids[i]!, jid]), undo }
    },
  },
  {
    name: 'displaceSubtree',
    covers: (u) => u.kind === 'region',
    applicable: (e, pinned) => movableRegionIds(e, pinned).length >= 1,
    propose: (e, pinned, rng, D) => {
      const rids = movableRegionIds(e, pinned)
      if (rids.length === 0) return null
      const rid = rids[Math.floor(rng() * rids.length)]!
      const carriers = subtreeCarriers(e, rid)
      const undo = savePoses(e, carriers)
      const radius = e.regions.get(rid)?.radius ?? 10 * e.scale
      const r = rangeAmp(D, radius)
      const a = rng() * 2 * Math.PI
      const dx = Math.cos(a) * r, dy = Math.sin(a) * r
      for (const c of carriers) { const b = e.bodies.get(c)!; b.pos = { x: b.pos.x + dx, y: b.pos.y + dy } }
      return { moved: new Set(carriers), undo }
    },
  },
  {
    name: 'displaceJunction',
    covers: (u) => u.kind === 'junction',
    // junctions are internal routing DOFs with no body id — `pinned` (a body-id
    // set) never pins them; a junction is movable whenever any wire has one.
    applicable: (e) => { for (const [, w] of e.wires) if (w.net.junctions.length > 0) return true; return false },
    propose: (e, _pinned, rng, D) => {
      const targets: { wid: WireId; w: WireView; j: number }[] = []
      for (const [wid, w] of e.wires) for (let j = 0; j < w.net.junctions.length; j++) targets.push({ wid, w, j })
      if (targets.length === 0) return null
      const { wid, w, j } = targets[Math.floor(rng() * targets.length)]!
      const saved = { ...w.net.junctions[j]! }
      const undo = (): void => { w.net.junctions[j] = { ...saved } }
      const r = rangeAmp(D, wireBoundRadius(e, w))
      const a = rng() * 2 * Math.PI
      w.net.junctions[j] = { x: saved.x + Math.cos(a) * r, y: saved.y + Math.sin(a) * r }
      return { moved: new Set<string>(), wids: new Set([wid]), undo }
    },
  },
  {
    name: 'swapSubtrees',
    covers: (u) => u.kind === 'region',
    applicable: (e, pinned) => siblingGroups(e, pinned).length >= 1,
    propose: (e, pinned, rng, D) => {
      const groups = siblingGroups(e, pinned)
      if (groups.length === 0) return null
      const g = groups[Math.floor(rng() * groups.length)]!
      const i = Math.floor(rng() * g.length)
      const r1 = g[i]!
      const c1 = e.regions.get(r1)!.center
      // VPR interchange rule at subtree scale: swap siblings within the D-window
      const near = g.filter((rid, k) => {
        if (k === i) return false
        const c = e.regions.get(rid)!.center
        const span = e.regions.get(r1)!.radius + e.regions.get(rid)!.radius
        return Math.hypot(c.x - c1.x, c.y - c1.y) <= Math.max(2 * span, D * 4 * frameHalf(e))
      })
      if (near.length === 0) return null
      const r2 = near[Math.floor(rng() * near.length)]!
      const c2 = e.regions.get(r2)!.center
      const dx = c2.x - c1.x, dy = c2.y - c1.y
      const car1 = subtreeCarriers(e, r1), car2 = subtreeCarriers(e, r2)
      const undo = savePoses(e, [...car1, ...car2])
      for (const c of car1) { const b = e.bodies.get(c)!; b.pos = { x: b.pos.x + dx, y: b.pos.y + dy } }
      for (const c of car2) { const b = e.bodies.get(c)!; b.pos = { x: b.pos.x - dx, y: b.pos.y - dy } }
      return { moved: new Set([...car1, ...car2]), undo }
    },
  },
]

/** The frame half-extent (the D-window's full-range scale); falls back to the
    content's own extent before a frame exists. */
function frameHalf(e: Engine): number {
  return e.frame?.half ?? 40 * e.scale
}

// ---- the basin-hopping search ----------------------------------------------

/** Default module seed for the worker's optimizer (tests pass explicit seeds). */
const DEFAULT_SEED = 0x1234abcd
/** Probe batch for temperature calibration: T0 is the typical (median)
    basin-floor |ΔE| over this many seeded hops at the seed basin. Each probe now
    costs a FULL relaxation (a basin hop), so the batch is 16 — the smallest that
    still gives a stable median (vs 64 on the raw landscape where a probe was a
    single cheap delta). The median (not the mean) is the typical hop: |ΔE_basin|
    is heavy-tailed (a hop into a wall relaxes to a far worse floor), and the
    median gives the typical hop acceptance ~e^-1, the calibration goal. */
const PROBE_BATCH = 16
/** Per-epoch geometric cooling: T ← 0.95·T. */
const COOL = 0.95
/** Chain moves per movable DOF per temperature. Moves are delta-priced
    (milliseconds), so the epoch returns to the pre-basin-hopping ratified
    value: enough samples per DOF for the epoch's acceptance-rate statistic
    (the range limiter's input) to be meaningful. */
const EPOCH_PER_DOF = 8
/** Reheat floor: reheat once T falls below T0/1000. */
const REHEAT_FLOOR = 1 / 1000
/** Consecutive fruitless reheats before dropping to low duty. 8 covers both
    restart flavors (best-perturb / fresh) four times each. */
const LOW_DUTY_REHEATS = 8
/** Settle steps per incremental-descent PUBLISH quantum (Phase 0). Relaxing the
    seed / incumbent publishes its monotone descent every this-many steps so the
    app shows it settling from the first frames (app-mode frames run no node
    descent — the frame-lightness law — so without this the visible layout sits
    raw-kinked until the first best). Publishing on a FIXED STEP quantum (not a
    wall-clock slice) makes the published descent sequence a pure function of the
    scene — deterministic and robust to how ticks slice wall-time. 50 ≈ a
    display frame's worth of descent (~40 ms at the ~1 ms/settleStep the routing
    layer targets), so the app sees ~frame-cadence updates; it is a
    publish-granularity knob (any value gives the same final basin floor), not a
    quality knob. Descent has no randomness, so every published descent state is
    on the scene's own downhill path, never a perturbation. */
const RELAX_PUBLISH_STEPS = 50

const eps = (x: number): number => 1e-9 * (Math.abs(x) + 1)
const EMPTY: ReadonlySet<string> = new Set()

export class LayoutOptimizer {
  readonly #seed: number
  #rng: Rng
  #scratch: Engine | null = null
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
  /** The search phase. Every tick advances ONE atomic unit of the current
      phase so a worker message handler never blocks:
      - 'descend': streamed seed/incumbent polish — deterministic solver in
        RELAX_PUBLISH_STEPS quanta, each quantum published (monotone, on the
        scene's own downhill path);
      - 'polish': SILENT rest-certification of a chain candidate or restart
        (same solver, no intermediate publishes — chain states are not on a
        monotone path); publishes only its certified rest;
      - 'chain': the unified Metropolis chain, one move per unit. */
  #phase: 'descend' | 'polish' | 'chain' = 'descend'
  /** Greedy-descent range factor (the descend phase's own D; the chain's #D
      is calibrated separately after certification). */
  #descentD = 1
  /** The scene's largest displacement unit (bodies, regions, wires, drawn
      rotation) — when D times this is at the sensing floor, every proposal is
      floor-scale and a zero-accept sweep means no sensed descent remains. */
  #descentMaxUnit = 0
  /** The persistent exact-delta evaluator over the scratch (rebuilt whenever a
      solver phase or restart moves the scratch outside the chain's commits). */
  #st: ScoreState | null = null
  /** Range factor D ∈ (0, 1]: every move kind's amplitude scale, adapted per
      epoch by VPR's rule toward the published 0.44 acceptance target. */
  #D = 1
  /** Warmup |dE| magnitudes: the FIRST PROBE_BATCH chain moves are accepted
      unconditionally (the standard T=∞ annealing start) and their magnitudes
      calibrate T0 (median — |dE| is heavy-tailed). */
  #warmupMags: number[] = []
  /** Moves taken at the current temperature; cool + adapt D at epoch end. */
  #movesThisEpoch = 0
  /** Accepts at the current temperature (the range limiter's statistic; an
      epoch accepting nothing also triggers a reheat). */
  #epochAccepts = 0

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

  /** Always searching — basin hopping never exhausts. */
  get searching(): boolean { return true }
  /** In low duty: the worker spaces epochs a few seconds apart (still searching). */
  get lowDuty(): boolean { return this.#lowDuty }
  /** Current annealing temperature (for the status debug seam). */
  get temperature(): number { return this.#T }

  /** The live layout is offered as a possibly-better incumbent. MONOTONE
      best-store (USER law: only the best yet found is stored): the worker's best
      and the client's mirrored best diverge asynchronously, so this can be handed
      a score ABOVE the worker's true best (a stale/racy adopt) — ignore it then,
      the worker's best is already better and the frame approaches IT. Only a
      genuinely better live layout becomes the new incumbent (adopted, relaxed
      incrementally via Phase 0, re-calibrated). */
  adoptLive(e: Engine, score: number): void {
    if (this.#best !== null && score >= this.#best.score - eps(this.#best.score)) return
    const scratch = this.#scratch
    if (scratch === null) { this.#best = layoutSnapshot(e, score); return }
    applyLayoutSnapshot(scratch, layoutSnapshot(e, 0))
    recomputeRegions(scratch)
    this.#best = layoutSnapshot(e, score)
    this.#T = 0
    this.#T0 = 0
    this.#enterDescent()
    this.#reheatsSinceImprove = 0
    this.#lowDuty = false
  }

  /** One budgeted slice of asynchronous search. Advances ONE atomic unit of the
      current phase per iteration — one descent quantum, one calibration probe,
      or one hop — so a worker message handler never blocks for a whole 16-probe
      calibration or an E-hop epoch (each is a full relaxation; acks/syncs would
      stall). Runs units until the wall budget is spent (always at least one), or
      exactly one unit in low duty. Returns whether the published best improved. */
  tick(_pinned: ReadonlySet<string> | null, budgetMs: number): boolean {
    if (this.#scratch === null || this.#best === null) return false
    const t0 = performance.now()
    let improved = false
    do {
      if (this.#stepUnit()) improved = true
    } while (!this.#lowDuty && performance.now() - t0 < budgetMs)
    return improved
  }

  // -- internals --

  /** THE ONLY publish gate — the monotone best-store invariant lives here (USER
      law: only the best yet found is stored). Snapshots the scratch as the new
      best iff its full `layoutScore` is strictly below the stored best; every
      publish path (descent quanta, accepted hops) goes through it, so a settle
      wobble (walkWires optimizes rod cost, not the separation term, so a step can
      raise the full score) can never publish an uphill state. Returns whether
      the best improved. */
  #publishIfBetter(score: number): boolean {
    if (this.#best !== null && score >= this.#best.score - eps(this.#best.score)) return false
    this.#best = layoutSnapshot(this.#scratch!, score)
    return true
  }

  /** One atomic unit of work, dispatched by phase. Returns whether best improved. */
  #stepUnit(): boolean {
    switch (this.#phase) {
      case 'descend': return this.#descentQuantum()
      case 'polish': return this.#polishQuantum()
      case 'chain': return this.#chainMove()
    }
  }

  #enterDescent(): void {
    this.#phase = 'descend'
    this.#st = null
    this.#descentD = 1
    this.#descentMaxUnit = 0
    this.#warmupMags = []
    this.#movesThisEpoch = 0
    this.#epochAccepts = 0
  }

  /** One PUBLISH quantum of the streamed seed/incumbent descent: a GREEDY
      (accept-only-downhill) sweep of the chain — one expected visit per DOF,
      delta-priced — published at the quantum boundary, so the app watches the
      seed untangle through strictly-improving states from the first slices.
      The range factor shrinks by the same acceptance-rate rule the chain
      uses; when a whole sweep at floor-scale amplitudes accepts nothing, no
      sensed descent remains and the deterministic solver takes over ONCE (the
      silent polish: it finishes any residue the move set cannot express and
      its final sweep is the rest certificate). This replaces running the
      full deterministic solver per quantum, whose per-step cost on dense
      scenes (exhaustive coordinate trials) consumed entire search budgets
      before the chain ever started (measured 2026-07-31). */
  #descentQuantum(): boolean {
    const scratch = this.#scratch!, pinned = this.#pinned, rng = this.#rng
    if (this.#st === null) {
      recomputeRegions(scratch)
      this.#st = mkScoreState(scratch)
      let u = 0
      for (const b of scratch.bodies.values()) u = Math.max(u, (b.discR + 2) * scratch.scale, Math.PI * b.discR * scratch.scale)
      for (const [, g] of scratch.regions) u = Math.max(u, g.radius)
      for (const [, w] of scratch.wires) if (w.net.junctions.length > 0) u = Math.max(u, wireBoundRadius(scratch, w))
      this.#descentMaxUnit = u
    }
    const st = this.#st
    const kinds = MOVE_REGISTRY.filter((m) => m.applicable(scratch, pinned))
    if (kinds.length === 0) { this.#phase = 'polish'; return false }
    const n = Math.max(1, this.#dofCount())
    let accepts = 0
    for (let k = 0; k < n; k++) {
      const kind = kinds[Math.floor(rng() * kinds.length)]!
      const p = kind.propose(scratch, pinned, rng, this.#descentD)
      if (p === null) continue
      recomputeRegions(scratch)
      const mr = applyMove(scratch, st, p.moved, p.wids ?? null)
      // material improvement only (the solver gates' own epsilon): float-dust
      // accepts at floor amplitudes would keep the descent phase alive forever
      if (mr.dE < -eps(st.total)) { mr.commit(); accepts++ } else { p.undo(); mr.abort() }
    }
    const improved = this.#publishIfBetter(st.total)
    const R = accepts / n
    this.#descentD = Math.min(1, this.#descentD * (1 - 0.44 + R))
    if (accepts === 0 && this.#descentD * this.#descentMaxUnit <= FD_PROBE) this.#phase = 'polish'
    return improved
  }

  /** One SILENT quantum of candidate/restart polishing: same solver, no
      intermediate publishes. At rest: publish the certified score if it beats
      the best, and resume the chain from the polished state. */
  #polishQuantum(): boolean {
    const scratch = this.#scratch!, pinned = this.#pinned
    let atRest = false
    for (let s = 0; s < RELAX_PUBLISH_STEPS; s++) {
      if (!settleStep(scratch, pinned)) { atRest = true; break }
    }
    if (!atRest) return false
    recomputeRegions(scratch)
    const score = layoutScore(scratch)
    const improved = this.#publishIfBetter(score)
    if (improved) { this.#reheatsSinceImprove = 0; this.#lowDuty = false }
    this.#enterChain()
    return improved
  }

  /** Enter (or re-enter) the chain from a certified rest: rebuild the exact
      evaluator; keep the schedule (T, T0, D) unless it was never calibrated. */
  #enterChain(): void {
    recomputeRegions(this.#scratch!)
    this.#st = mkScoreState(this.#scratch!)
    this.#phase = 'chain'
  }

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
    // Enter Phase 0: publish the seed as the initial best (= the live layout, no
    // jump), then relax it incrementally in tick() so the app sees it settle —
    // the seed is NOT relaxed here (that would block sync and hide the descent).
    const seedScore = layoutScore(scratch)
    this.#best = layoutSnapshot(scratch, seedScore)
    this.#rng = mkRng(this.#seed)
    this.#T = 0
    this.#T0 = 0
    this.#enterDescent()
    this.#restartParity = 0
    this.#reheatsSinceImprove = 0
    this.#lowDuty = false
  }

  /** The DOF count driving the epoch length and reheat cadence. */
  #dofCount(): number {
    return nonPinnedIds(this.#scratch!, this.#pinned).length + this.#scratch!.childrenOf.size
  }

  /** One move of the unified chain: propose at range D, price by the EXACT
      incremental delta, Metropolis-accept, commit or undo. Epoch bookkeeping
      at EPOCH_PER_DOF·DOF moves: adapt D by the measured acceptance rate
      (VPR's rule, target 0.44 — fpl97, verified), cool T, reheat on the floor
      or a zero-accept epoch. A committed state strictly below the published
      best enters the SILENT polish phase for rest certification. */
  #chainMove(): boolean {
    const scratch = this.#scratch!, pinned = this.#pinned, rng = this.#rng
    const st = this.#st!
    const kinds = MOVE_REGISTRY.filter((m) => m.applicable(scratch, pinned))
    if (kinds.length === 0) return false
    const kind = kinds[Math.floor(rng() * kinds.length)]!
    const p = kind.propose(scratch, pinned, rng, this.#D)
    this.#movesThisEpoch++
    let improvedCandidate = false
    if (p !== null) {
      recomputeRegions(scratch)
      const mr = applyMove(scratch, st, p.moved, p.wids ?? null)
      const dE = mr.dE
      const warming = this.#warmupMags.length < PROBE_BATCH
      if (warming) {
        this.#warmupMags.push(Math.abs(dE))
        if (this.#warmupMags.length >= PROBE_BATCH) {
          const mags = [...this.#warmupMags].sort((a, b) => a - b)
          this.#T0 = mags[mags.length >> 1]!
          this.#T = this.#T0
        }
      }
      const T = this.#T
      const accept = warming || dE < 0 || (T > 0 && rng() < Math.exp(-dE / T))
      if (accept) {
        mr.commit()
        this.#epochAccepts++
        if (this.#best !== null && st.total < this.#best.score - eps(this.#best.score)) {
          // rest-certify before any publish (USER law: published bests are
          // sensible layouts — here, PROVEN rests)
          this.#phase = 'polish'
          improvedCandidate = false
        }
      } else {
        p.undo()
        mr.abort()
      }
    }
    if (this.#warmupMags.length >= PROBE_BATCH && this.#movesThisEpoch >= EPOCH_PER_DOF * this.#dofCount()) {
      const R = this.#epochAccepts / this.#movesThisEpoch
      // the RANGE LIMITER: Dlimit_new = Dlimit_old · (1 − 0.44 + R_accept),
      // clamped — VPR's published rule and target
      this.#D = Math.min(1, this.#D * (1 - 0.44 + R))
      this.#T *= COOL
      if (this.#T < this.#T0 * REHEAT_FLOOR || this.#epochAccepts === 0) this.#reheat()
      this.#movesThisEpoch = 0
      this.#epochAccepts = 0
    }
    return improvedCandidate
  }

  /** Reheat: alternate seeded restarts — (a) the incumbent best (the following
      epoch at T0 is its one-epoch perturbation) and (b) a fresh random
      arrangement relaxed to its basin. Resets T to T0; after enough fruitless
      reheats, drops to low duty. */
  #reheat(): void {
    this.#reheatsSinceImprove++
    if (this.#reheatsSinceImprove >= LOW_DUTY_REHEATS) this.#lowDuty = true
    const parity = this.#restartParity++ % 2
    if (parity === 0) {
      applyLayoutSnapshot(this.#scratch!, this.#best!)
      recomputeRegions(this.#scratch!)
      this.#restorePinned()
      this.#enterChain()
    } else {
      // a fresh arrangement is raw — certify it through the silent polish
      // before the chain continues from it
      this.#freshArrangement()
      this.#st = null
      this.#phase = 'polish'
    }
    this.#T = this.#T0
    this.#D = 1
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
      construction-time overlap projection. The caller relaxes it to a basin. */
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
