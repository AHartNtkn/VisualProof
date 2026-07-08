/**
 * MULTIPORT JUNCTION RENDERING — the round-8 · D soap-film Steiner tree with
 * tangential tributary merging, the ONLY junction look the user ever approved
 * (recovered from git bfddd17; user verdict 2026-07-07: promote as-is, with NO
 * rendered dots at branch points — the branching structure is the only visual).
 *
 * A ≥3-leg interior junction (a hub POINT in the plan-24 engine) is drawn as a
 * soap-film Steiner tree: free internal points relax under unit tension per
 * incident branch (Plateau's 120° junctions) with node-disc keep-out, then split/
 * merge to a degree-3 tree; at each branch point the two most-opposite branches
 * flow through as one tangent-continuous stream and the others merge TANGENT to it
 * (a tributary joining a river). The wire model is UNTOUCHED — this is a VIEW-ONLY
 * pass over the engine's live junction terminals; it moves no physics DOF.
 *
 * The soap trees are PERSISTENT per engine (a view-layer WeakMap, not engine/physics
 * state): the split/merge distances are a hysteresis pair, so a fresh tree every
 * frame would flap the topology (a no-snap violation). A junction seen for the first
 * time converges from its star seed; afterwards it tracks its terminals smoothly.
 */
import type { WireId } from '../kernel/diagram/diagram'
import type { Vec2 } from './vec'
import type { Engine } from './engine'
import { resolveLeg } from './engine'
import type { Shape, Theme } from './paint'

const wrap = (x: number): number => Math.atan2(Math.sin(x), Math.cos(x))

// ---- Hobby G1 interpolating bezier (recovered from src/view/wires.ts @ bfddd17) --
type WirePath = { from: Vec2; c1: Vec2; c2: Vec2; to: Vec2 }
function hobbyRho(theta: number, phi: number): number {
  const a = Math.sqrt(2), b = 1 / 16, c = (3 - Math.sqrt(5)) / 2
  const num = 2 + a * (Math.sin(theta) - b * Math.sin(phi)) * (Math.sin(phi) - b * Math.sin(theta)) * (Math.cos(theta) - Math.cos(phi))
  const den = 1 + (1 - c) * Math.cos(theta) + c * Math.cos(phi)
  return num / den
}
function hobbyBezier(pa: Vec2, ta: number, pb: Vec2, tb: number): WirePath {
  const chord = Math.atan2(pb.y - pa.y, pb.x - pa.x)
  const d = Math.hypot(pb.x - pa.x, pb.y - pa.y)
  const theta = wrap(ta - chord)
  const phi = wrap(chord - (tb + Math.PI))
  const ra = Math.abs(hobbyRho(theta, phi)) * d / 3
  const rb = Math.abs(hobbyRho(phi, theta)) * d / 3
  return { from: pa, c1: { x: pa.x + Math.cos(ta) * ra, y: pa.y + Math.sin(ta) * ra }, c2: { x: pb.x + Math.cos(tb) * rb, y: pb.y + Math.sin(tb) * rb }, to: pb }
}
function sampleBezier(p: WirePath, out: Vec2[], n = 24): void {
  for (let i = 0; i <= n; i++) {
    const t = i / n, u = 1 - t
    out.push({
      x: u * u * u * p.from.x + 3 * u * u * t * p.c1.x + 3 * u * t * t * p.c2.x + t * t * t * p.to.x,
      y: u * u * u * p.from.y + 3 * u * u * t * p.c1.y + 3 * u * t * t * p.c2.y + t * t * t * p.to.y,
    })
  }
}

// ---- soap-film Steiner machinery (ui-lab/multiport.ts @ bfddd17, VERBATIM) --------
type SoapTree = { pts: Vec2[]; adj: number[][]; nT: number }
type Obstacle = { pos: Vec2; r: number }
type Terminal = { p: Vec2; tangent: number; key: string | null }
const SPAWN_DIST = 1.0, MERGE_DIST = 0.3, TENSION_STEP = 0.25, COS120 = Math.cos((2 * Math.PI) / 3)

function nodeObstacles(e: Engine): Obstacle[] {
  const out: Obstacle[] = []
  const sc = e.scale
  for (const b of e.bodies.values()) {
    if (b.kind === 'junction' || b.kind === 'anchor') continue
    out.push({ pos: b.pos, r: b.discR * sc + 1 })
  }
  return out
}
function terminalTangent(t: Terminal, toward: Vec2): number {
  return t.key === null ? Math.atan2(toward.y - t.p.y, toward.x - t.p.x) : t.tangent
}
function mkSoapTree(terminals: readonly Terminal[], hubPos: Vec2): SoapTree {
  const pts = terminals.map((x) => ({ ...x.p }))
  pts.push({ ...hubPos })
  return { pts, adj: [...terminals.map(() => [terminals.length]), terminals.map((_, i) => i)], nT: terminals.length }
}
/** Closest point on segment a→b to p, and its parameter t∈[0,1]. */
function closestOnSeg(p: Vec2, a: Vec2, b: Vec2): { q: Vec2; t: number } {
  const abx = b.x - a.x, aby = b.y - a.y
  const t = Math.max(0, Math.min(1, ((p.x - a.x) * abx + (p.y - a.y) * aby) / (abx * abx + aby * aby || 1)))
  return { q: { x: a.x + t * abx, y: a.y + t * aby }, t }
}
function relaxSoap(t: SoapTree, obstacles: readonly Obstacle[]): void {
  for (let iter = 0; iter < 6; iter++) {
    for (let v = t.nT; v < t.pts.length; v++) {
      let fx = 0, fy = 0
      for (const n of t.adj[v]!) {
        const dx = t.pts[n]!.x - t.pts[v]!.x, dy = t.pts[n]!.y - t.pts[v]!.y
        const d = Math.hypot(dx, dy)
        if (d < 1e-9) continue
        fx += dx / d; fy += dy / d
      }
      for (const o of obstacles) {
        const dx = t.pts[v]!.x - o.pos.x, dy = t.pts[v]!.y - o.pos.y
        const d = Math.hypot(dx, dy)
        if (d >= o.r || d < 1e-9) continue
        const push = (o.r - d) / o.r
        fx += (dx / d) * push * 2; fy += (dy / d) * push * 2
      }
      // the film FLOWS AROUND obstacles: if any EDGE incident to v crosses an
      // obstacle, push v perpendicular so the edge bends around it (a soap film
      // never sits ON a peg). This is what keeps a trunk from running behind a node.
      for (const n of t.adj[v]!) {
        for (const o of obstacles) {
          const { q } = closestOnSeg(o.pos, t.pts[v]!, t.pts[n]!)
          const dx = q.x - o.pos.x, dy = q.y - o.pos.y
          const d = Math.hypot(dx, dy)
          if (d >= o.r) continue
          const push = (o.r - d) / o.r
          const ux = d < 1e-9 ? 1 : dx / d, uy = d < 1e-9 ? 0 : dy / d
          fx += ux * push * 3; fy += uy * push * 3
        }
      }
      t.pts[v] = { x: t.pts[v]!.x + fx * TENSION_STEP, y: t.pts[v]!.y + fy * TENSION_STEP }
    }
  }
}
function reshapeSoap(t: SoapTree): void {
  // SPLIT: a branch point holding two branches tighter than 120° sheds them
  for (let v = t.nT; v < t.pts.length; v++) {
    const nbrs = t.adj[v]!
    if (nbrs.length < 4) continue
    let bi = -1, bj = -1, best = COS120
    for (let i = 0; i < nbrs.length; i++) for (let j = i + 1; j < nbrs.length; j++) {
      const a = t.pts[nbrs[i]!]!, b = t.pts[nbrs[j]!]!
      const ua = { x: a.x - t.pts[v]!.x, y: a.y - t.pts[v]!.y }
      const ub = { x: b.x - t.pts[v]!.x, y: b.y - t.pts[v]!.y }
      const la = Math.hypot(ua.x, ua.y), lb = Math.hypot(ub.x, ub.y)
      if (la < 1e-9 || lb < 1e-9) continue
      const cos = (ua.x * ub.x + ua.y * ub.y) / (la * lb)
      if (cos > best) { best = cos; bi = i; bj = j }
    }
    if (bi < 0) continue
    const a = nbrs[bi]!, b = nbrs[bj]!
    const dir = Math.atan2((t.pts[a]!.y + t.pts[b]!.y) / 2 - t.pts[v]!.y, (t.pts[a]!.x + t.pts[b]!.x) / 2 - t.pts[v]!.x)
    const w = t.pts.length
    t.pts.push({ x: t.pts[v]!.x + Math.cos(dir) * SPAWN_DIST, y: t.pts[v]!.y + Math.sin(dir) * SPAWN_DIST })
    t.adj.push([a, b, v])
    t.adj[v] = nbrs.filter((n) => n !== a && n !== b)
    t.adj[v]!.push(w)
    for (const x of [a, b]) t.adj[x] = t.adj[x]!.map((n) => (n === v ? w : n))
  }
  // MERGE: an internal edge that tension collapsed folds back into one point
  for (let v = t.nT; v < t.pts.length; v++) {
    for (const w of [...t.adj[v]!]) {
      if (w < t.nT || w <= v) continue
      const d = Math.hypot(t.pts[w]!.x - t.pts[v]!.x, t.pts[w]!.y - t.pts[v]!.y)
      if (d >= MERGE_DIST) continue
      t.adj[v] = [...t.adj[v]!.filter((n) => n !== w), ...t.adj[w]!.filter((n) => n !== v)]
      for (const n of t.adj[w]!) if (n !== v) t.adj[n] = t.adj[n]!.map((m) => (m === w ? v : m))
      t.adj[w] = []
      return
    }
  }
}
/** The TARGET trunk axis at a branch point: the bisector direction of the two
    most-opposite branches (round8-d.ts @ bfddd17 — the "through-trunk" direction). */
function targetAxis(pts: readonly Vec2[], adj: readonly number[][], v: number): number {
  const nbrs = adj[v]!
  const dirs = nbrs.map((n) => Math.atan2(pts[n]!.y - pts[v]!.y, pts[n]!.x - pts[v]!.x))
  if (nbrs.length < 2) return dirs[0] ?? 0
  let bi = 0, bj = 1, best = -Infinity
  for (let i = 0; i < dirs.length; i++) for (let j = i + 1; j < dirs.length; j++) {
    const score = -Math.abs(Math.abs(wrap(dirs[i]! - dirs[j]!)) - Math.PI)
    if (score > best) { best = score; bi = i; bj = j }
  }
  return Math.atan2(Math.sin(dirs[bi]!) - Math.sin(dirs[bj]!), Math.cos(dirs[bi]!) - Math.cos(dirs[bj]!))
}
/** Outgoing tangents at a branch point given a trunk AXIS `u`: each branch leaves
    toward the nearer trunk end (u or u+π), pulled from its own radial direction by the
    weight |cos(dir−u)| — plan-24's continuous merge (Subsystem 3 / relax.ts trunkTarget).
    Weight 1 for a leg aligned with the axis (it becomes the trunk, leaving along u),
    fading to 0 for a leg perpendicular to it (which stays radial). The weight vanishing
    exactly at the perpendicular is what makes the merge CONTINUOUS: the hard u↔u+π side
    flip a leg undergoes as it crosses perpendicular happens where its effect is zero, so
    no tangent ever jumps. At a relaxed ~120° Steiner point every leg is near-aligned or
    near-opposite (weight ≈ 1), so the rendered tangents equal round-8 D's hard rule —
    the STILLS are unchanged; only motion through the crossing is smoothed. A degree-1
    internal point (a transient) leaves radially. */
function tangentsFromAxis(pts: readonly Vec2[], adj: readonly number[][], v: number, u: number): Map<number, number> {
  const out = new Map<number, number>()
  const nbrs = adj[v]!
  for (const n of nbrs) {
    const dir = Math.atan2(pts[n]!.y - pts[v]!.y, pts[n]!.x - pts[v]!.x)
    if (nbrs.length < 2) { out.set(n, dir); continue }
    const side = Math.abs(wrap(dir - u)) <= Math.PI / 2 ? u : u + Math.PI
    const weight = Math.abs(Math.cos(wrap(dir - u)))
    out.set(n, dir + weight * wrap(side - dir))
  }
  return out
}

// ---- terminal extraction from the current plan-24 engine -------------------------
type MJunction = { wid: WireId; hubPos: Vec2; terminals: Terminal[]; hubBodyId: string | null }
/** EVERY ≥3-arm junction is drawn as a soap tributary tree — whatever its hub
    representation. The hub center is a POINT (a pure interior k-ary junction, or a
    k≥2 boundary junction) or a BODY (a ∀ via-body whose scope-homed body IS the
    branch hub — plan-24 engine.ts). Each hub arm is a terminal: a bind arm gives
    its PORT end (p0, th0, port key); a boundary SLOT arm gives its frame-edge end
    with the frame-normal tangent (a non-null sentinel key so terminalTangent uses
    it, not a radial guess). 1–2-arm wires keep the base elastica rendering.
    Before this fix a body-hub (∀) or boundary junction fell through to the star
    render — "an edge node with everything attached" (USER 2026-07-07). */
function extractJunctions(e: Engine): MJunction[] {
  const out: MJunction[] = []
  for (const [wid, w] of e.wires) {
    if (w.hub === null) continue
    const hubLegs = w.legs.filter((l) => l.b.kind === 'hub')
    if (hubLegs.length < 3) continue
    const hubBodyId = w.hub.kind === 'body' ? w.hub.bodyId : null
    const hubPos = w.hub.kind === 'point' ? { ...w.hub.pos } : { ...e.bodies.get(w.hub.bodyId)!.pos }
    const terminals: Terminal[] = hubLegs.map((leg) => {
      const s = resolveLeg(e, w, leg)
      // a bind arm carries its port key (fixed exit normal); a slot arm carries the
      // frame normal via th0 (sentinel key so it is honoured, not radialised).
      const key = leg.a.kind === 'bind' ? w.binds[leg.a.i]!.key : leg.a.kind === 'slot' ? 'slot' : null
      return { p: { ...s.p0 }, tangent: s.th0, key }
    })
    out.push({ wid, hubPos, terminals, hubBodyId })
  }
  return out
}

/** The wids drawn as a soap junction (paintWires skips their star legs). */
export function junctionWids(e: Engine): Set<WireId> {
  return new Set(extractJunctions(e).map((m) => m.wid))
}

/** The junction-hub BODY ids (∀ via-bodies) that are now soap trees — paint must
    NOT draw a structural dot on these (only genuine degree-1 ∃ loose ends keep a
    dot). A boundary/interior POINT hub has no body, so it contributes nothing. */
export function junctionHubBodies(e: Engine): Set<string> {
  const out = new Set<string>()
  for (const m of extractJunctions(e)) if (m.hubBodyId !== null) out.add(m.hubBodyId)
  return out
}

// Persistent per-engine soap trees (VIEW-layer state, not physics): the hysteresis
// split/merge needs a carried tree or the topology flaps. WeakMap → auto-freed with
// the engine; a rewrite builds a NEW engine (fresh trees seeded from carried terminals).
// `drawn` holds the DRAWN internal-branch-point positions (see DRAW_CAP below);
// `axes` the CARRIED trunk axis per branch-point index (see the argmax-flip fix).
const soapCache = new WeakMap<Engine, Map<WireId, { tree: SoapTree; nT: number; drawn: Vec2[]; axes: Map<number, number> }>>()

// The converged soap-film Steiner tree is DISCONTINUOUS in its terminals: at certain
// configurations a branch point slides through a near-degenerate spot and the minimal
// tree JUMPS (measured ~10 wu in one frame under a realistic settle — more relax rounds
// do NOT smooth it; it is a genuine bifurcation of the minimiser, inherent to the method).
// That is a no-snap violation (USER LAW: NO SNAPPING, PERIOD). So the DRAWN branch points
// track their converged targets under the SAME per-frame continuity bound the physics
// uses for every DOF (WIREP.travelCap) — presentation only: at rest the drawn points sit
// exactly on the converged tree (identical look), and a bifurcation glides over a few
// frames instead of snapping. The terminal (port) ends are never eased — they stay exact.
const DRAW_CAP = 0.55 // = WIREP.travelCap, the physics per-frame continuity bound (× scale)

// Per-FRAME memo of the computed tributary geometry, keyed on e.tick. The drawn
// branch points EASE once per frame (DRAW_CAP), so the geometry must be computed
// exactly ONCE per frame — but BOTH the base painter AND the hover/select
// highlight need it (the highlight must trace the SAME tributary curves, not the
// old star legs — USER 2026-07-07: "why are there two different ways to calculate
// that shape?"). Memoising per tick lets both callers share one computation with
// no double-ease. Geometry is theme-free; the stroke is applied by the wrappers.
const polyMemo = new WeakMap<Engine, { tick: number; byWid: Map<WireId, Vec2[][]> }>()

/** The tributary POLYLINES per junction wire (theme-free geometry) — the SINGLE
    source of junction shape. Computed once per frame (memoised on e.tick); the
    per-frame ease of the drawn branch points happens on the first call each tick. */
export function junctionPolylines(e: Engine): Map<WireId, Vec2[][]> {
  const memo = polyMemo.get(e)
  if (memo !== undefined && memo.tick === e.tick) return memo.byWid
  const byWid = computeJunctionPolylines(e)
  polyMemo.set(e, { tick: e.tick, byWid })
  return byWid
}

/** The soap-tributary Shape[] for every ≥3-arm junction — sampled Hobby curves
    only, NO branch-point dots (USER 2026-07-07). Wraps junctionPolylines with the
    theme stroke; the hover highlight wraps the same geometry with its own stroke. */
export function junctionShapes(e: Engine, st: Theme): Shape[] {
  const glow = st.wireGlow ? st.wire : null
  const shapes: Shape[] = []
  for (const polys of junctionPolylines(e).values()) {
    for (const pts of polys) shapes.push({ kind: 'polyline', pts, stroke: st.wire, width: st.wireW, glow })
  }
  return shapes
}

function computeJunctionPolylines(e: Engine): Map<WireId, Vec2[][]> {
  let trees = soapCache.get(e)
  if (trees === undefined) { trees = new Map(); soapCache.set(e, trees) }
  const obstacles = nodeObstacles(e)
  const byWid = new Map<WireId, Vec2[][]>()
  const cap = DRAW_CAP * e.scale
  for (const m of extractJunctions(e)) {
    const polys: Vec2[][] = []
    byWid.set(m.wid, polys)
    let entry = trees.get(m.wid)
    let fresh = false
    if (entry === undefined || entry.nT !== m.terminals.length) {
      entry = { tree: mkSoapTree(m.terminals, m.hubPos), nT: m.terminals.length, drawn: [], axes: new Map() }
      trees.set(m.wid, entry)
      fresh = true
    }
    const t = entry.tree
    m.terminals.forEach((x, i) => { t.pts[i] = { ...x.p } }) // live terminal positions
    // converge from the star seed on first sight; track smoothly afterwards
    const rounds = fresh ? 60 : 8
    for (let r = 0; r < rounds; r++) { relaxSoap(t, obstacles); reshapeSoap(t) }
    // DRAWN internal points ease toward the converged targets under the continuity cap
    // (see DRAW_CAP). Each EXISTING branch point steps at most `cap` toward its target so
    // a bifurcation glides, never snaps; a genuinely NEW point (a reshape SPLIT appends
    // it at a fresh index) takes its converged position directly (it spawns ≤ SPAWN_DIST
    // from its parent — a small, sub-cap-class addition, not a jump of an existing line).
    // NEVER a global reset — that is what re-introduced the snap on every split.
    const dpts: Vec2[] = t.pts.map((p) => ({ ...p })) // terminals exact; internals overwritten below
    for (let v = t.nT; v < t.pts.length; v++) {
      const cur = fresh ? undefined : entry.drawn[v]
      const tgt = t.pts[v]!
      if (cur === undefined) { dpts[v] = { ...tgt }; continue }
      const dx = tgt.x - cur.x, dy = tgt.y - cur.y, d = Math.hypot(dx, dy)
      dpts[v] = d <= cap || d < 1e-9 ? { ...tgt } : { x: cur.x + (dx / d) * cap, y: cur.y + (dy / d) * cap }
    }
    entry.drawn = dpts.map((p) => ({ ...p }))
    // tangents + curves are built from the DRAWN points, so the whole junction is
    // continuous frame-to-frame (the tangent rule reads the eased branch geometry).
    // The trunk AXIS per branch point is CARRIED and eased toward its target under an
    // angular cap tied to the physics continuity bound (DRAW_CAP over the branch's mean
    // arm length): under smooth motion the true axis moves less than the cap and tracks
    // freely; when the most-opposite pair changes (the target jumps ~π/2 — the argmax
    // that used to SNAP the trunk), the eased axis glides over a few frames instead.
    // The axis is eased MOD π (u and u+π are the same axis), so a pair END-swap is a
    // no-op. At rest the eased axis equals the target → the drawn tangents (hence the
    // stills) are IDENTICAL to round-8 D's argmax rendering.
    const tangents = new Map<number, Map<number, number>>()
    for (let v = t.nT; v < dpts.length; v++) {
      if (t.adj[v]!.length === 0) continue
      const uTarget = targetAxis(dpts, t.adj, v)
      const prev = fresh ? undefined : entry.axes.get(v)
      let u: number
      if (prev === undefined) u = uTarget
      else {
        let d = wrap(uTarget - prev)
        if (d > Math.PI / 2) d -= Math.PI; else if (d < -Math.PI / 2) d += Math.PI // axis (mod π)
        let arm = 0, k = 0
        for (const n of t.adj[v]!) { arm += Math.hypot(dpts[n]!.x - dpts[v]!.x, dpts[n]!.y - dpts[v]!.y); k++ }
        const angCap = cap / Math.max(arm / Math.max(k, 1), 1)
        u = prev + Math.max(-angCap, Math.min(angCap, d))
      }
      entry.axes.set(v, u)
      tangents.set(v, tangentsFromAxis(dpts, t.adj, v, u))
    }
    // a Hobby curve loops when an endpoint tangent deviates from the chord by ≥ 90°;
    // clamp internal tangents strictly inside that bound (the merge look survives —
    // near the branch point the curve still leaves along the trunk)
    const MAXDEV = Math.PI / 2 - 0.15
    const clampTo = (tangent: number, chord: number): number => chord + Math.max(-MAXDEV, Math.min(MAXDEV, wrap(tangent - chord)))
    for (let v = 0; v < dpts.length; v++) {
      for (const n of t.adj[v]!) {
        if (n <= v) continue
        const chord = Math.atan2(dpts[n]!.y - dpts[v]!.y, dpts[n]!.x - dpts[v]!.x)
        const tv = v < t.nT ? terminalTangent(m.terminals[v]!, dpts[n]!) : clampTo(tangents.get(v)!.get(n)!, chord)
        const tn = n < t.nT ? terminalTangent(m.terminals[n]!, dpts[v]!) : clampTo(tangents.get(n)!.get(v)!, chord + Math.PI)
        const pts: Vec2[] = []
        sampleBezier(hobbyBezier(dpts[v]!, tv, dpts[n]!, tn), pts)
        polys.push(pts)
      }
    }
  }
  return byWid
}
