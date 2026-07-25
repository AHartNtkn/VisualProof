import type { WireId } from '../kernel/diagram/diagram'
import type { Vec2 } from './vec'
import type { Engine, WireView } from './engine'
import {
  ROUTE_CLEAR, routeObstacles, routeBounds, wireTerminalPoints, wireTerminalBCs,
} from './engine'
import { mkFreeSpace, route } from './route/freespace'
import type { FreeSpace } from './route/freespace'
import { edgeCurvePts, rodCost } from './route/curve'
import { rodBeta, contentEnergy, recomputeRegions, segSeparationBetween } from './relax'
import type { FrozenEdge } from './relax'

/**
 * INCREMENTAL EXACT ENERGY DELTA (plan Task 3). `wireEnergy(e)+contentEnergy(e)`
 * rebuilds the whole disc-visibility routing structure and the all-pairs wire
 * separation every call; the local solver's acceptance gates and the annealer
 * only ever perturb a handful of bodies per trial. This evaluator tracks the
 * energy incrementally: a `ScoreState` caches, per wire, its routed rod energy
 * and its drawn curve segments; a move re-evaluates ONLY the wires a body
 * displacement can reach and re-adds ONLY the separation pairs those wires
 * touch. The result is EXACT (float tolerance), not approximate — the delta is
 * the accept/reject oracle, so any inexactness would silently change decisions.
 *
 * THE UNCHANGED-WIRE LEMMA. A wire whose terminals did not move keeps its exact
 * energy under a body displacement iff every moved obstacle disc is irrelevant
 * to its routing problem. `route(fs, pu, pv)` picks the cheapest path and
 * `rodCost` charges obstacle surcharge along the drawn curve; both read a disc
 * only where a candidate path or the curve comes within the disc's radius. Every
 * point q of any path we would ever prefer over the cached route (cost L)
 * satisfies f(q) = |pu−q| + |q−pv| ≤ L (a point on a pu→pv path of length ≤ L),
 * and f is 2-Lipschitz, so a disc of radius r whose centre c has f(c) > L + 2r
 * cannot touch any such path or the cached curve — at its OLD centre it was not
 * blocking a cheaper route, at its NEW centre it does not block or surcharge the
 * cached one. Testing min over {old, new} centre against L + 2r therefore catches
 * every wire whose energy can change (route opened, route blocked, or curve
 * surcharge), and skips the rest with a proof, not a guess. L is taken as the
 * max of the route cost and the largest f over the cached curve samples, so the
 * clamped-anchor curve ends (which reach slightly past the routed escape points)
 * are covered too.
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
  /** The frozen route waypoints of every edge — the envelope-probe evaluator's
      input (`frozenWireEnergy`), captured by the SAME full eval that seeds the
      caches so the caller needs no second `wireEnergyCapture`. Rebuilt on commit. */
  frozen: FrozenEdge[]
}

const f2 = (a: Vec2, c: Vec2, b: Vec2): number =>
  Math.hypot(a.x - c.x, a.y - c.y) + Math.hypot(c.x - b.x, c.y - b.y)

const isObstacle = (kind: string): boolean => kind === 'ref' || kind === 'term' || kind === 'atom'

/** Evaluate one wire against a FreeSpace: its routed rod energy, drawn curve
    segments, and per-edge reach data. The exact per-wire slice of
    `wireEnergyCapture` (relax.ts) — the same route → curve → rodCost pipeline. */
function evalWire(e: Engine, wid: WireId, w: WireView, fs: FreeSpace, beta: number, clear: number): WireCache {
  const terms = wireTerminalPoints(e, w)
  if (terms.length < 2) return { E: 0, segs: [], edges: [], frozen: [] }
  const bcs = wireTerminalBCs(e, w)
  const pos = (v: number): Vec2 => (v < terms.length ? terms[v]! : w.net.junctions[v - terms.length]!)
  let E = 0
  const segs: Seg[] = []
  const edges: EdgeReach[] = []
  const frozen: FrozenEdge[] = []
  for (const [u, v] of w.net.edges) {
    const pu = pos(u), pv = pos(v)
    const r = route(fs, pu, pv)
    const pts = edgeCurvePts(u < bcs.length ? bcs[u]! : null, v < bcs.length ? bcs[v]! : null, r.pts, clear)
    E += rodCost(pts, fs, beta)
    for (let i = 0; i + 1 < pts.length; i++) segs.push({ a: pts[i]!, b: pts[i + 1]! })
    frozen.push({ wid, u, v, interior: r.pts.slice(1, -1) })
    // reach bound: any path we would prefer has length ≤ route cost, and every
    // drawn-curve point q has f(q) ≤ its own arc length — take the larger so both
    // the route-change and the curve-surcharge cases are bounded.
    let L = r.cost
    for (const q of pts) { const fq = f2(pu, q, pv); if (fq > L) L = fq }
    edges.push({ pu, pv, L })
  }
  return { E, segs, edges, frozen }
}

/** ONE full eval, captured for incremental replay. Caches per-wire energy and
    curve segments, the pairwise separation total, contentEnergy, the obstacle
    positions, and the tracked total. */
export function mkScoreState(e: Engine): ScoreState {
  recomputeRegions(e)
  const fs = mkFreeSpace(routeObstacles(e), routeBounds(e))
  const beta = rodBeta(e)
  const clear = ROUTE_CLEAR * e.scale
  const wires = new Map<WireId, WireCache>()
  const order: WireId[] = []
  const frozen: FrozenEdge[] = []
  let wireETotal = 0
  for (const [wid, w] of e.wires) {
    const c = evalWire(e, wid, w, fs, beta, clear)
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
  return { wires, order, wireETotal, sepTotal, contentE, pos, total: wireETotal + sepTotal + contentE, frozen }
}

/** The result of a tentative move: its exact energy delta and the two ways to
    resolve it. `commit` folds the recomputed pieces into the caches (the caller
    keeps the mutated engine); `abort` discards them (the caller un-mutates the
    engine). */
export type MoveResult = { readonly dE: number; commit(): void; abort(): void }

/**
 * Exact energy delta for a body displacement. `moved` = the ids of the bodies
 * whose pose (position or rotation) the CALLER already changed on `e`. Recomputes
 * exactly (a) wires with a terminal on a moved body, (b) wires whose routing a
 * moved obstacle disc can reach (the unchanged-wire lemma), (c) the separation
 * pairs those wires touch, and (d) contentEnergy in full (cheap). Everything else
 * is provably identical and stays cached.
 */
export function applyMove(e: Engine, st: ScoreState, moved: ReadonlySet<string>): MoveResult {
  const sc = e.scale

  // (a) terminal-affected: a wire with a bind body or end body among the moved.
  const affected = new Set<WireId>()
  for (const [wid, w] of e.wires) {
    let hit = w.endBodyId !== null && moved.has(w.endBodyId)
    if (!hit) for (const bd of w.binds) { if (moved.has(bd.body)) { hit = true; break } }
    if (hit) affected.add(wid)
  }

  // moved obstacle discs: old centre (cached), new centre (live), inflated radius.
  const movedObs: { o: Vec2; p: Vec2; r: number }[] = []
  for (const id of moved) {
    const b = e.bodies.get(id)
    if (b === undefined || !isObstacle(b.kind)) continue
    movedObs.push({ o: st.pos.get(id)!, p: b.pos, r: (b.discR + ROUTE_CLEAR) * sc })
  }

  // (b) obstacle-affected: a not-yet-affected wire whose reach a moved disc enters.
  if (movedObs.length > 0) {
    for (const wid of st.order) {
      if (affected.has(wid)) continue
      const edges = st.wires.get(wid)!.edges
      let hit = false
      for (const ed of edges) {
        for (const D of movedObs) {
          const reach = ed.L + 2 * D.r
          if (Math.min(f2(ed.pu, D.o, ed.pv), f2(ed.pu, D.p, ed.pv)) <= reach) { hit = true; break }
        }
        if (hit) break
      }
      if (hit) affected.add(wid)
    }
  }

  // recompute the affected wires against a fresh FreeSpace over the CURRENT
  // obstacles (0.09 ms; its all-pairs visibility is lazy — it only builds if an
  // affected route is actually blocked, and only the affected routes query it).
  const beta = rodBeta(e)
  const clear = ROUTE_CLEAR * sc
  const newWire = new Map<WireId, WireCache>()
  let dWireE = 0
  if (affected.size > 0) {
    const fs = mkFreeSpace(routeObstacles(e), routeBounds(e))
    for (const wid of affected) {
      const c = evalWire(e, wid, e.wires.get(wid)!, fs, beta, clear)
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
