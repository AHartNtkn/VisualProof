import type { RegionId, WireId } from '../kernel/diagram/diagram'
import type { BodyKind, Engine, WireView } from './engine'
import { mkEngine, subtreeCarriers, frameBounds, wireTerminalPoints } from './engine'
import {
  settleStep, contentEnergy, wireEnergy, recomputeRegions, resolveOverlaps, establishFrame,
} from './relax'
import type { WireNet } from './route/network'
import type { Vec2 } from './vec'

/**
 * WHOLE-LAYOUT GLOBAL OPTIMIZATION (USER ruling 2026-07-24): the system seeks
 * a GLOBAL optimum of the entire layout, asynchronously; only the best layout
 * found so far is stored; each frame the visible layout approaches the best
 * known. The searcher is BASIN HOPPING (Wales–Doye, USER ruling): the Monte
 * Carlo chain runs on the TRANSFORMED landscape E(localmin(x)) — every proposal
 * is relaxed to its local minimum by plain descent BEFORE acceptance, so the
 * heavy machinery only ever JUMPS BETWEEN WELLS and never descends slopes. This
 * replaces the raw-landscape annealer whose intermediate published states were
 * un-relaxed and absurd; here every accepted state is a rest, so every published
 * best is a sensible layout.
 *
 * The search runs on a SCRATCH engine (never the visible one). One hop takes the
 * current basin minimum, applies ONE hierarchical move (single body, rotation,
 * body swap, rigid subtree shift, sibling-subtree swap) from a seeded
 * xorshift128 stream (NO Math.random, NO Date.now), relaxes the perturbed
 * layout to rest, and accepts by the Metropolis rule comparing BASIN-FLOOR
 * energies only. An accepted hop's rest state becomes the new basin minimum and
 * is published immediately if it beats the best. There is NO exhaustion state:
 * after 8 fruitless reheats the searcher drops to a low duty (one epoch per few
 * seconds) but never claims optimality.
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
  | { readonly kind: 'endDot'; readonly id: string }
  | { readonly kind: 'junction'; readonly wid: WireId; readonly j: number }

/** Every movable unit of an engine: each body (by kind), each region subtree
    (via childrenOf), each wire-owned end dot (via endBodyId), and each wire
    junction (a routed Steiner point — a positional DOF the local walk can only
    settle within its basin, so crossing a junction cusp is a search-layer move). */
export function movableUnits(e: Engine): MovableUnit[] {
  const units: MovableUnit[] = []
  for (const [id, b] of e.bodies) units.push({ kind: 'carrier', carrierKind: b.kind, id })
  for (const rid of e.childrenOf.keys()) units.push({ kind: 'region', id: rid })
  for (const [, w] of e.wires) if (w.endBodyId !== null) units.push({ kind: 'endDot', id: w.endBodyId })
  for (const [wid, w] of e.wires) for (let j = 0; j < w.net.junctions.length; j++) units.push({ kind: 'junction', wid, j })
  return units
}

/** A tentative move: the ids whose pose it changed and its exact undo. Basin
    hopping restores a rejected hop from the whole-basin snapshot (relaxation
    moves more than the move did), so it does not use `undo`; the field is the
    move library's own contract, unchanged from the annealer. */
type Proposal = {
  readonly moved: Set<string>
  /** The RELAX BLOCK for this move (annealing redesign D2): the bodies allowed
      to settle after the perturbation; everything else is frozen. Defaults to
      `moved`. A junction hop names its wire's terminal bodies (the junction is
      not a body, but its wire must walk and its neighborhood may adapt). */
  readonly block?: ReadonlySet<string>
  undo(): void
}

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

/** Octave ladder for displacement magnitude. On the TRANSFORMED (basin-hopping)
    landscape a sub-basin jitter is pointless — the relaxation that follows every
    move maps any within-well displacement straight back to the same floor, so a
    fraction-of-a-disc hop is wasted work (measured on the acceptance trap: only
    the ≥1× subtree hops that clear a disc change the basin at all). So the
    smallest amplitude is 1×(discR+2)×scale; the ladder is {1, 2, 4}, four→three
    octaves, still bounded above by the frame half-extent (~8 disc radii). */
const OCTAVES = [1, 2, 4] as const
const octaveBase = (rng: Rng): number => OCTAVES[Math.floor(rng() * OCTAVES.length)]!

const isPortBearing = (kind: BodyKind): boolean =>
  kind === 'ref' || kind === 'atom' || kind === 'identity'

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

/** The move registry — DATA the search proposes from and the coverage test
    checks. Displacement covers every body and end dot; subtree moves cover
    every region; rotation covers port-bearing bodies; body/subtree swaps add
    coordinated exchanges no single-body move can express. */
export const MOVE_REGISTRY: readonly MoveKind[] = [
  {
    name: 'displaceBody',
    covers: (u) => u.kind === 'carrier' || u.kind === 'endDot',
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
    covers: (u) => u.kind === 'carrier' && isPortBearing(u.carrierKind),
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
    covers: (u) => u.kind === 'carrier' || u.kind === 'endDot',
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
    name: 'displaceJunction',
    covers: (u) => u.kind === 'junction',
    // junctions are internal routing DOFs with no body id — `pinned` (a body-id
    // set) never pins them; a junction is movable whenever any wire has one.
    applicable: (e) => { for (const [, w] of e.wires) if (w.net.junctions.length > 0) return true; return false },
    propose: (e, _pinned, rng) => {
      const targets: { w: WireView; j: number }[] = []
      for (const [, w] of e.wires) for (let j = 0; j < w.net.junctions.length; j++) targets.push({ w, j })
      if (targets.length === 0) return null
      const { w, j } = targets[Math.floor(rng() * targets.length)]!
      const saved = { ...w.net.junctions[j]! }
      const undo = (): void => { w.net.junctions[j] = { ...saved } }
      // octave ladder over the wire's own extent: a positional hop big enough to
      // clear a routing barrier (the junction cusp is a barrier-separated basin);
      // the relaxation that follows settles the junction into the new basin, and
      // Metropolis keeps it only if that basin is lower. `moved` is empty — a
      // junction is not a body — and the rejected-hop restore comes from the
      // whole-basin snapshot (which captures junctions), not this undo.
      const r = octaveBase(rng) * wireBoundRadius(e, w)
      const a = rng() * 2 * Math.PI
      w.net.junctions[j] = { x: saved.x + Math.cos(a) * r, y: saved.y + Math.sin(a) * r }
      const block = new Set<string>(w.binds.map((bd) => bd.body))
      if (w.endBodyId !== null) block.add(w.endBodyId)
      return { moved: new Set<string>(), block, undo }
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
/** Hops per movable DOF per temperature. On the transformed landscape ONE hop
    is a whole relaxation (hundreds of settle steps), so 8×DOF hops per
    temperature is wall-prohibitive; one hop per DOF per temperature is the
    smallest schedule that still visits every DOF once before cooling. */
const EPOCH_PER_DOF = 1
/** Reheat floor: reheat once T falls below T0/1000. */
const REHEAT_FLOOR = 1 / 1000
/** Consecutive fruitless reheats before dropping to low duty. 8 covers both
    restart flavors (best-perturb / fresh) four times each. */
const LOW_DUTY_REHEATS = 8
/** Relaxation backstop: a hop relaxes the perturbed layout to rest (settleStep
    until it reports no motion), bounded here so a hop that scattered into a
    slowly-converging configuration abandons it and stays cheap. A good basin
    settles in a few hundred steps (measured 758 on the acceptance escape); any
    value above that yields the same basins, it only caps wasted work — not a
    quality knob. A wall-clock cap is rejected: it would make the accepted
    sequence machine-dependent and break determinism. */
const RELAX_REST_CAP = 2000
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
  /** Energy of the current basin floor (layoutScore of #scratch, at rest). */
  #basinE = 0
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
  /** The search phase. Every tick advances ONE atomic unit of the current phase
      (one descent quantum, one calibration probe, or one hop) so a worker
      message handler never blocks for many relaxations:
      - 'descend': relax the seed / adopted incumbent to its basin floor,
        publishing its monotone descent per RELAX_PUBLISH_STEPS quantum;
        no publish) — they cannot all live in one handler;
      - 'hop': basin hopping (publish on Metropolis acceptance). */
  #phase: 'descend' | 'hop' = 'descend'
  /** Warmup |ΔE_basin| magnitudes: the FIRST PROBE_BATCH hops are accepted
      unconditionally (the standard T=∞ annealing start) and their magnitudes
      calibrate T0 — the same median statistic as dedicated probes, but the
      relaxations ADVANCE the chain instead of being discarded, so there is no
      dead window between the descent floor and the first hop. */
  #warmupMags: number[] = []
  /** Hops taken at the current temperature; cool + maybe reheat at #epochLen. */
  #hopsThisEpoch = 0
  /** Accepts at the current temperature (reheat when an epoch accepts nothing). */
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
    this.#basinE = score
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
      case 'hop': return this.#hopUnit()
    }
  }

  #enterDescent(): void {
    this.#phase = 'descend'
    this.#warmupMags = []
    this.#hopsThisEpoch = 0
    this.#epochAccepts = 0
  }

  /** One PUBLISH quantum of incremental descent (Phase 0): RELAX_PUBLISH_STEPS
      plain settle steps, then publish the improved state. Every published state
      is on the scene's own monotone downhill path — never a random perturbation.
      At rest, fixes the basin floor and advances to the calibration phase. */
  #descentQuantum(): boolean {
    const scratch = this.#scratch!, pinned = this.#pinned
    let atRest = false
    for (let s = 0; s < RELAX_PUBLISH_STEPS; s++) {
      if (!settleStep(scratch, pinned)) { atRest = true; break }
    }
    recomputeRegions(scratch)
    const score = layoutScore(scratch)
    const improved = this.#publishIfBetter(score)
    if (atRest) { this.#basinE = score; this.#phase = 'hop'; this.#warmupMags = []; this.#T0 = 0; this.#T = 0 }
    return improved
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
    this.#basinE = layoutScore(scratch)
    this.#best = layoutSnapshot(scratch, this.#basinE)
    this.#rng = mkRng(this.#seed)
    this.#T = 0
    this.#T0 = 0
    this.#enterDescent()
    this.#restartParity = 0
    this.#reheatsSinceImprove = 0
    this.#lowDuty = false
  }

  /** Relax the scratch to a local minimum by plain descent (settleStep until no
      motion, bounded by the backstop) — the core of the transformed landscape. */
  #relaxToRest(): void {
    const scratch = this.#scratch!, pinned = this.#pinned
    for (let s = 0; s < RELAX_REST_CAP; s++) {
      if (!settleStep(scratch, pinned)) break
    }
    recomputeRegions(scratch)
  }

  /** BLOCK-LOCAL relaxation (annealing redesign D2): settle ONLY the block the
      hop perturbed, with every other body totally frozen. The measured defect
      this kills: a hop's GLOBAL relaxation moved bodies the move never touched
      as far as the ones it did (median 5.81 vs 5.53 wu, 2026-07-28), so
      accepting a hop scrambled organized regions it never addressed — and the
      relaxation cost scaled with the scene instead of the block. Wales–Doye's
      original freezing idiom, on the existing pinned plumbing. */
  #relaxBlock(block: ReadonlySet<string>): void {
    const scratch = this.#scratch!, pinned = this.#pinned
    const frozen = new Set<string>()
    for (const id of scratch.bodies.keys()) if (!block.has(id)) frozen.add(id)
    for (let s = 0; s < RELAX_REST_CAP; s++) {
      if (!settleStep(scratch, pinned, frozen)) break
    }
    recomputeRegions(scratch)
  }

  /** The DOF count driving the epoch length and reheat cadence. */
  #dofCount(): number {
    return nonPinnedIds(this.#scratch!, this.#pinned).length + this.#scratch!.childrenOf.size
  }

  /** One hop of the proposal phase, with per-hop epoch bookkeeping: after an
      epoch's worth of hops (EPOCH_PER_DOF·DOF) cool the temperature and reheat
      if it fell through the floor or the epoch accepted nothing. Slicing to one
      hop per unit keeps a tick from blocking for a whole epoch of relaxations. */
  #hopUnit(): boolean {
    const r = this.#hop()
    this.#hopsThisEpoch++
    if (r.accepted) this.#epochAccepts++
    if (this.#warmupMags.length >= PROBE_BATCH && this.#hopsThisEpoch >= EPOCH_PER_DOF * this.#dofCount()) {
      this.#T *= COOL
      if (this.#T < this.#T0 * REHEAT_FLOOR || this.#epochAccepts === 0) this.#reheat()
      this.#hopsThisEpoch = 0
      this.#epochAccepts = 0
    }
    return r.improved
  }

  /** One basin hop: perturb the current basin minimum by one move, relax to
      rest, and accept by Metropolis on the basin-floor energy delta. An accepted
      rest state becomes the new basin minimum (and is published if it beats the
      best); a rejected hop restores the previous basin from its snapshot. */
  #hop(): { accepted: boolean; improved: boolean } {
    const scratch = this.#scratch!, pinned = this.#pinned, rng = this.#rng
    const kinds = MOVE_REGISTRY.filter((m) => m.applicable(scratch, pinned))
    if (kinds.length === 0) return { accepted: false, improved: false }
    const saved = layoutSnapshot(scratch, 0)
    const kind = kinds[Math.floor(rng() * kinds.length)]!
    const p = kind.propose(scratch, pinned, rng)
    if (p === null) return { accepted: false, improved: false }
    recomputeRegions(scratch)
    const block = p.block ?? p.moved
    if (block.size > 0 && block.size < scratch.bodies.size) this.#relaxBlock(block)
    else this.#relaxToRest()
    let newE = layoutScore(scratch)
    const dE = newE - this.#basinE
    // warmup: the first PROBE_BATCH hops accept unconditionally (T = ∞ start)
    // and their |ΔE| magnitudes fix T0 = median — no dedicated probe phase
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
      // an accepted block-hop's state is a BLOCK rest. Published bests must be
      // GLOBAL rests (USER law: every published best is a sensible layout), so
      // a candidate improvement is POLISHED — fully relaxed — before the
      // publish gate; the chain adopts the polished floor either way (a free
      // strict improvement, and accommodation the block freeze deferred).
      if (this.#best !== null && newE < this.#best.score - eps(this.#best.score)) {
        this.#relaxToRest()
        newE = layoutScore(scratch)
      }
      this.#basinE = newE
      const improved = this.#publishIfBetter(newE)
      if (improved) { this.#reheatsSinceImprove = 0; this.#lowDuty = false }
      return { accepted: true, improved }
    }
    applyLayoutSnapshot(scratch, saved)
    recomputeRegions(scratch)
    return { accepted: false, improved: false }
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
      this.#basinE = this.#best!.score
    } else {
      this.#freshArrangement()
      this.#relaxToRest()
      this.#basinE = layoutScore(this.#scratch!)
    }
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
