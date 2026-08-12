import type { RegionId, WireId } from '../kernel/diagram/diagram'
import type { Vec2 } from './vec'
import type { Engine, WireView, WireSpaces } from './engine'
import { isBodyObstacle, wireRouteSpaces, wireTerminalPoints, wireTerminalBCs } from './engine'
import { route } from './route/freespace'
import type { Disc } from './route/freespace'
import { curveEnergy, solveEdgeCurve } from './route/curve'
import type { NearSpace } from './route/curve'
import { rodBeta, contentEnergy, segSeparationBetween, wireNearSpaces, WIREP } from './relax'
import type { FrozenEdge } from './relax'

/**
 * INCREMENTAL EXACT ENERGY DELTA (annealing redesign D1; resurrected from
 * c7932b8 and extended for per-wire cut-obstacle spaces).
 * `wireEnergy(e)+contentEnergy(e)` rebuilds the whole routing structure and the
 * all-pairs wire separation every call; the local solver's acceptance gates and
 * the search chain only ever perturb a handful of bodies per trial. This
 * evaluator tracks the energy incrementally: a `ScoreState` caches, per wire,
 * its routed rod energy and its drawn curve segments; a move re-evaluates ONLY
 * the wires the move can reach and re-adds ONLY the separation pairs those
 * wires touch. The result is EXACT (float tolerance), not approximate — the
 * delta is the accept/reject oracle, so any inexactness would silently change
 * decisions.
 *
 * THE UNCHANGED-WIRE LEMMA. A wire whose terminals did not move keeps its exact
 * energy under a body displacement iff every moved obstacle disc is irrelevant
 * to its routing problem. `route(fs, pu, pv)` picks the cheapest path and
 * `rodCost` charges obstacle surcharge along the drawn curve; both read a disc
 * only where a candidate path or the curve comes within the disc's radius.
 * Every point q of any path we would ever prefer over the cached route (cost L)
 * satisfies f(q) = |pu−q| + |q−pv| ≤ L, and f is 2-Lipschitz, so a disc of
 * radius r whose centre c has f(c) > L + 2r cannot touch any such path or the
 * cached curve. A disc is irrelevant iff BOTH its old incarnation (c₀, r₀) and
 * its new one (c₁, r₁) fail their reach tests. L is the max of the route cost
 * and the largest f over the cached curve samples.
 *
 * REGION CIRCLES ARE OBSTACLES TOO (2026-07-30 design): a wire's space
 * includes the drawn circles of the cuts it is not inside, and those circles
 * MOVE when their member bodies move. The lemma applies to them unchanged —
 * a changed circle is a moved (possibly resized) disc — scoped to the wires
 * whose forbidden set contains that region.
 */

/** A drawn curve segment (endpoints only — the separation quadrature samples it). */
type Seg = { readonly a: Vec2; readonly b: Vec2 }

/** Per routed edge: the routing endpoints (ellipse foci) and the reach bound L
    of the unchanged-wire lemma. */
type EdgeReach = { readonly pu: Vec2; readonly pv: Vec2; readonly L: number }

/** One wire's cached contribution: its routed rod energy, its drawn curve
    segments (for separation), per-edge reach data (for the skip test), and the
    frozen route waypoints (for the gradient probes' envelope evaluator). */
type WireCache = { E: number; segs: Seg[]; edges: EdgeReach[]; frozen: FrozenEdge[] }

export type ScoreState = {
  /** Per-wire cache, keyed by wire id (every wire in the engine, in insertion order). */
  readonly wires: Map<WireId, WireCache>
  /** Stable wire order — the index that keeps each separation pair counted once. */
  readonly order: WireId[]
  /** Per-wire forbidden region ids (shared arrays — identity from wireRouteSpaces). */
  readonly forbiddenRids: ReadonlyMap<WireId, readonly RegionId[]>
  /** The INFLATED forbidden circle of every non-sheet region at the tracked
      configuration (r = drawn radius + ROUTE_CLEAR·scale). */
  readonly regionDiscs: Map<RegionId, Disc>
  /** Σ per-wire routed rod energy. */
  wireETotal: number
  /** Σ inter-wire separation over all wire pairs. */
  sepTotal: number
  /** contentEnergy(e) at the tracked configuration (recomputed whole per move). */
  contentE: number
  /** Cached body centres — the OLD obstacle positions the next move tests against. */
  readonly pos: Map<string, Vec2>
  /** The tracked total = wireETotal + sepTotal + contentE. */
  total: number
  /** The frozen route waypoints of every edge (envelope-probe input). */
  frozen: FrozenEdge[]
}

const f2 = (a: Vec2, c: Vec2, b: Vec2): number =>
  Math.hypot(a.x - c.x, a.y - c.y) + Math.hypot(c.x - b.x, c.y - b.y)

/** The engine's current DRAWN forbidden circles, one per non-sheet region
    (the nearness energy measures against drawn geometry; the reach margin in
    `discReaches` covers the routing clearance). */
function currentRegionDiscs(e: Engine): Map<RegionId, Disc> {
  const out = new Map<RegionId, Disc>()
  for (const [rid, g] of e.regions) {
    if (e.d.regions[rid]!.kind === 'sheet') continue
    out.set(rid, { c: { x: g.center.x, y: g.center.y }, r: g.radius })
  }
  return out
}

/** Evaluate one wire against ITS routing space: routed rod energy, drawn curve
    segments, and per-edge reach data. The exact per-wire slice of
    `wireEnergyCapture` (relax.ts) — the same route → curve → rodCost pipeline. */
function evalWire(e: Engine, wid: WireId, w: WireView, spaces: WireSpaces, ns: NearSpace, beta: number): WireCache {
  const terms = wireTerminalPoints(e, w)
  if (terms.length < 2) return { E: 0, segs: [], edges: [], frozen: [] }
  const fs = spaces.space(wid)
  const bcs = wireTerminalBCs(e, w)
  const pos = (v: number): Vec2 => (v < terms.length ? terms[v]! : w.net.junctions[v - terms.length]!)
  let E = 0
  const segs: Seg[] = []
  const edges: EdgeReach[] = []
  const frozen: FrozenEdge[] = []
  for (const [u, v] of w.net.edges) {
    const pu = pos(u), pv = pos(v)
    const r = route(fs, pu, pv)
    const sol = solveEdgeCurve(u < bcs.length ? bcs[u]! : null, v < bcs.length ? bcs[v]! : null, pu, pv, r.hugs, ns, beta)
    E += curveEnergy(sol.pts, ns, beta)
    for (let i = 0; i + 1 < sol.pts.length; i++) segs.push({ a: sol.pts[i]!, b: sol.pts[i + 1]! })
    frozen.push({ wid, u, v, anchors: sol.anchors })
    let L = r.cost
    for (const q of sol.pts) { const fq = f2(pu, q, pv); if (fq > L) L = fq }
    edges.push({ pu, pv, L })
  }
  return { E, segs, edges, frozen }
}

/** ONE full eval, captured for incremental replay. The caller must have
    recomputed regions. */
export function mkScoreState(e: Engine): ScoreState {
  const spaces = wireRouteSpaces(e)
  const nsOf = wireNearSpaces(e, spaces)
  const beta = rodBeta(e)
  const wires = new Map<WireId, WireCache>()
  const order: WireId[] = []
  const frozen: FrozenEdge[] = []
  let wireETotal = 0
  for (const [wid, w] of e.wires) {
    const c = evalWire(e, wid, w, spaces, nsOf(wid), beta)
    wires.set(wid, c)
    order.push(wid)
    wireETotal += c.E
    for (const fe of c.frozen) frozen.push(fe)
  }
  let sepTotal = 0
  for (let i = 0; i < order.length; i++) {
    const segsA = wires.get(order[i]!)!.segs
    if (segsA.length === 0) continue
    for (let j = i + 1; j < order.length; j++) {
      const segsB = wires.get(order[j]!)!.segs
      if (segsB.length === 0) continue
      sepTotal += segSeparationBetween(segsA, segsB, e.scale)
    }
  }
  const contentE = contentEnergy(e)
  const pos = new Map<string, Vec2>()
  for (const [id, b] of e.bodies) pos.set(id, { x: b.pos.x, y: b.pos.y })
  return {
    wires, order, forbiddenRids: spaces.forbiddenRids, regionDiscs: currentRegionDiscs(e),
    wireETotal, sepTotal, contentE, pos, total: wireETotal + sepTotal + contentE, frozen,
  }
}

/** The result of a tentative move: its exact energy delta and the two ways to
    resolve it. `commit` folds the recomputed pieces into the caches (the caller
    keeps the mutated engine); `abort` discards them (the caller un-mutates the
    engine). */
export type MoveResult = { readonly dE: number; commit(): void; abort(): void }

/** A moved/changed obstacle disc: old and new incarnation (radius may change
    for region circles). */
type MovedDisc = { readonly o: Vec2; readonly ro: number; readonly p: Vec2; readonly rn: number }

/** Unchanged-wire skip test, with the energy-drawn margin M: nearness reads a
    disc up to R beyond its boundary, and the curve solve's descent can move
    an anchor by at most Σ(R/2ᵏ) < 2R off its seed, so a disc farther than
    L + 2(r + 3R) from the edge's ellipse cannot touch the seed, any state the
    descent visits, or the nearness reach of either — the wire's solved curve
    and energy are bit-identical. */
const discReaches = (ed: EdgeReach, D: MovedDisc, M: number): boolean =>
  f2(ed.pu, D.o, ed.pv) <= ed.L + 2 * (D.ro + M) || f2(ed.pu, D.p, ed.pv) <= ed.L + 2 * (D.rn + M)

/**
 * Exact energy delta for a body pose change (position and/or rotation).
 * `moved` = the ids of the bodies whose pose the CALLER already changed on `e`,
 * with regions recomputed. Recomputes exactly (a) wires with a terminal on a
 * moved body, (b) wires whose routing a moved node disc or a CHANGED forbidden
 * region circle can reach (the unchanged-wire lemma), (c) the separation pairs
 * those wires touch, and (d) contentEnergy in full (cheap). Everything else is
 * provably identical and stays cached.
 */
export function applyMove(e: Engine, st: ScoreState, moved: ReadonlySet<string>, movedWires: ReadonlySet<WireId> | null = null): MoveResult {
  const sc = e.scale

  // (a) terminal-affected: a wire with a bind body or end body among the moved,
  // plus wires whose OWN state the caller changed (junction proposals).
  const affected = new Set<WireId>()
  if (movedWires !== null) for (const wid of movedWires) affected.add(wid)
  for (const [wid, w] of e.wires) {
    let hit = w.end !== null && moved.has(w.end.body)
    if (!hit) for (const bd of w.binds) { if (moved.has(bd.body)) { hit = true; break } }
    if (hit) affected.add(wid)
  }

  // moved node obstacle discs: old centre (cached), new centre (live). The
  // reach margin M covers both the routing clearance (< R) and the nearness
  // reach + solver wander, so the DRAWN radius is the right base.
  const M = 3 * WIREP.sepR * sc
  const movedObs: MovedDisc[] = []
  for (const id of moved) {
    const b = e.bodies.get(id)
    if (b === undefined || !isBodyObstacle(b)) continue
    const o = st.pos.get(id)!
    if (o.x === b.pos.x && o.y === b.pos.y) continue // rotation-only: disc unmoved
    const r = b.discR * sc
    movedObs.push({ o, ro: r, p: b.pos, rn: r })
  }

  // changed forbidden region circles (regions are derived; a body move drags
  // its ancestor circles). Diffed exactly against the tracked incarnation.
  const nowDiscs = currentRegionDiscs(e)
  const changedRegions = new Map<RegionId, MovedDisc>()
  for (const [rid, n] of nowDiscs) {
    const o = st.regionDiscs.get(rid)
    if (o === undefined) continue // structural change is not a pose move; caller rebuilds instead
    if (o.c.x !== n.c.x || o.c.y !== n.c.y || o.r !== n.r) {
      changedRegions.set(rid, { o: o.c, ro: o.r, p: n.c, rn: n.r })
    }
  }

  // (b) obstacle-affected: a not-yet-affected wire whose reach a moved node
  // disc enters, or whose OWN forbidden set contains a changed region circle
  // that enters its reach.
  if (movedObs.length > 0 || changedRegions.size > 0) {
    for (const wid of st.order) {
      if (affected.has(wid)) continue
      const edges = st.wires.get(wid)!.edges
      let hit = false
      for (const ed of edges) {
        for (const D of movedObs) { if (discReaches(ed, D, M)) { hit = true; break } }
        if (hit) break
        if (changedRegions.size > 0) {
          for (const rid of st.forbiddenRids.get(wid) ?? []) {
            const D = changedRegions.get(rid)
            if (D !== undefined && discReaches(ed, D, M)) { hit = true; break }
          }
        }
        if (hit) break
      }
      if (hit) affected.add(wid)
    }
  }

  // recompute the affected wires against fresh per-wire spaces over the CURRENT
  // obstacles (visibility is lazy — it only builds if an affected route is
  // actually blocked, and only the affected routes query it).
  const beta = rodBeta(e)
  const newWire = new Map<WireId, WireCache>()
  let dWireE = 0
  if (affected.size > 0) {
    const spaces = wireRouteSpaces(e)
    const nsOf = wireNearSpaces(e, spaces)
    for (const wid of affected) {
      const c = evalWire(e, wid, e.wires.get(wid)!, spaces, nsOf(wid), beta)
      newWire.set(wid, c)
      dWireE += c.E - st.wires.get(wid)!.E
    }
  }

  // (c) separation: subtract old, add new for every pair touching an affected wire.
  const idx = new Map<WireId, number>()
  st.order.forEach((wid, i) => idx.set(wid, i))
  const oldSegs = (wid: WireId): Seg[] => st.wires.get(wid)!.segs
  const newSegs = (wid: WireId): Seg[] => (affected.has(wid) ? newWire.get(wid)!.segs : st.wires.get(wid)!.segs)
  let dSep = 0
  for (const a of affected) {
    const ia = idx.get(a)!
    const aOld = oldSegs(a), aNew = newSegs(a)
    for (const b of st.order) {
      if (b === a) continue
      const bAff = affected.has(b)
      if (bAff && idx.get(b)! < ia) continue // count each affected–affected pair once
      const bOld = oldSegs(b), bNew = newSegs(b)
      dSep += segSeparationBetween(aNew, bNew, sc) - segSeparationBetween(aOld, bOld, sc)
    }
  }

  // (d) content: full recompute (measured ~0 ms). Caller has recomputed regions.
  const contentNew = contentEnergy(e)
  const dContent = contentNew - st.contentE

  const dE = dWireE + dSep + dContent
  return {
    dE,
    commit(): void {
      for (const [wid, c] of newWire) st.wires.set(wid, c)
      st.wireETotal += dWireE
      st.sepTotal += dSep
      st.contentE = contentNew
      for (const id of moved) {
        const b = e.bodies.get(id)
        if (b !== undefined) st.pos.set(id, { x: b.pos.x, y: b.pos.y })
      }
      for (const [rid, n] of nowDiscs) st.regionDiscs.set(rid, n)
      st.total = st.wireETotal + st.sepTotal + st.contentE
      if (newWire.size > 0) {
        const frozen: FrozenEdge[] = []
        for (const wid of st.order) for (const fe of st.wires.get(wid)!.frozen) frozen.push(fe)
        st.frozen = frozen
      }
    },
    abort(): void { /* caches untouched; caller restores the engine */ },
  }
}
