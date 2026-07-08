import type { WireId } from '../kernel/diagram/diagram'
import type { Vec2 } from './vec'
import type { Engine, Leg, LegEnd, WireLegEnd, WireView } from './engine'
import { resolveLeg, traceLeg, ascaleOf, DISC_R } from './engine'

/**
 * Wire geometry over the PLAN-22 massless elastica, pure — returns traced
 * polylines, paints nothing. Each leg IS the minimum-energy θ-quadratic
 * interpolant of its live boundary data (elastica.ts); rendering simply traces
 * it at paint resolution (n=30). Loops and kinks are unrepresentable, so the
 * traced line is always a smooth non-self-crossing curve leaving each port
 * perpendicular by construction. A boundary wire's leg reaches its FIXED frame
 * slot as an ordinary leg endpoint (plan 24 — no exterior connector, no exit
 * body). ∃/∀ ends and bare wires become existential dots.
 */

/** Trace resolution for painted legs (segments per leg). */
const PAINT_N = 30

export type LegGeom = { leg: Leg; pts: Vec2[] }
export type ExStub = { wid: WireId; from: Vec2; to: Vec2; dot: Vec2 }

/** The rendering identity of a leg terminal: real (body, key) at a port bind
    and the ∀ via-body hub; a wire-local id for a pure hub point, a boundary
    slot, or the ∃ tip body. Endpoint-level gestures (drag-join) read these. */
function endId(wid: WireId, w: WireView, end: WireLegEnd): LegEnd {
  switch (end.kind) {
    case 'bind': return { body: w.binds[end.i]!.body, key: w.binds[end.i]!.key }
    case 'tip': return { body: w.tipBodyId!, key: null }
    case 'slot': return { body: `w:${wid}:slot`, key: null }
    case 'hub': { const h = w.hub!; return h.kind === 'body' ? { body: h.bodyId, key: null } : { body: `w:${wid}:hub`, key: null } }
  }
}

/** Every drawable leg as a traced polyline. The traced curve is the wire — it
    starts ON the rim heading along the port normal and closes on its far end
    (another port, the branch/exit hub, or the ∃ tip), tangent range <= pi so it
    never loops. */
export function computeLegs(e: Engine): LegGeom[] {
  const out: LegGeom[] = []
  for (const [wid, w] of e.wires) {
    for (const leg of w.legs) {
      const s = resolveLeg(e, w, leg)
      const pts: Vec2[] = []
      traceLeg(s, pts, PAINT_N)
      out.push({ leg: { wid, from: endId(wid, w, leg.a), to: endId(wid, w, leg.b) }, pts })
    }
  }
  return out
}

/** Traced polyline for every leg (boundary legs included — a boundary leg reaches
    its fixed frame slot directly, plan 24). */
export function legPaths(e: Engine): { wid: WireId; pts: Vec2[] }[] {
  return computeLegs(e).map((g) => ({ wid: g.leg.wid, pts: g.pts }))
}

/** The node discs a drawn wire must skim AROUND (never cross): every ref/atom/term
    body at its clearance radius. A wire that ends ON a node attaches there — that
    node is excluded per-polyline in `routeAroundNodes` (an endpoint inside it). */
export function nodeDiscs(e: Engine): { c: Vec2; r: number }[] {
  const sc = e.scale
  const out: { c: Vec2; r: number }[] = []
  for (const b of e.bodies.values()) {
    if (b.kind !== 'ref' && b.kind !== 'atom' && b.kind !== 'term') continue
    // the DRAWN radius (what the eye sees), not the padded clearance disc: a wire
    // skims just outside the visible node. Refs draw at DISC_R; atoms/terms at
    // their outermost anatomy arc. A small margin keeps the arc off the ink.
    let drawn = DISC_R * sc
    if (b.kind !== 'ref' && b.geometry !== null) {
      let maxArc = 0
      for (const a of b.geometry.arcs) maxArc = Math.max(maxArc, a.r)
      drawn = maxArc * ascaleOf(b.kind) * sc
    }
    out.push({ c: b.pos, r: drawn })
  }
  return out
}

/** Point where segment p→q crosses circle (C,R) (q outside, p inside). */
function circleCross(inside: Vec2, outside: Vec2, C: Vec2, R: number): Vec2 {
  const dx = outside.x - inside.x, dy = outside.y - inside.y
  const fx = inside.x - C.x, fy = inside.y - C.y
  const a = dx * dx + dy * dy
  const b = 2 * (fx * dx + fy * dy)
  const c = fx * fx + fy * fy - R * R
  const disc = Math.max(0, b * b - 4 * a * c)
  const t = a < 1e-9 ? 0 : Math.min(1, Math.max(0, (-b + Math.sqrt(disc)) / (2 * a)))
  return { x: inside.x + dx * t, y: inside.y + dy * t }
}

/** Reroute one polyline so it skims AROUND a disc it would otherwise cross: the
    run inside the disc is replaced by an arc along the rim (the shorter way round),
    giving the semicircle-around-a-node look. A polyline that ENDS inside the disc
    attaches to that node and is left untouched. */
function routeOne(pts: readonly Vec2[], C: Vec2, R: number): readonly Vec2[] {
  const n = pts.length
  if (n < 3) return pts
  const inside = (p: Vec2): boolean => Math.hypot(p.x - C.x, p.y - C.y) < R
  // Maximal runs [i0..i1] of points inside the disc. A run touching an endpoint
  // (index 0 or n-1) is where the wire ATTACHES to this node — leave it; an
  // interior run is the wire passing UNDER the node — replace it with a rim arc.
  const runs: [number, number][] = []
  for (let i = 0; i < n; i++) {
    if (!inside(pts[i]!)) continue
    const start = i
    while (i + 1 < n && inside(pts[i + 1]!)) i++
    runs.push([start, i])
  }
  // Rebuild from the LAST interior run backwards so earlier indices stay valid.
  let out: Vec2[] = pts.slice()
  for (let r = runs.length - 1; r >= 0; r--) {
    const [i0, i1] = runs[r]!
    if (i0 === 0 || i1 === n - 1) continue // attachment run — the wire meets the rim here
    const A = circleCross(pts[i0]!, pts[i0 - 1]!, C, R)
    const B = circleCross(pts[i1]!, pts[i1 + 1]!, C, R)
    const a0 = Math.atan2(A.y - C.y, A.x - C.x)
    let d = Math.atan2(B.y - C.y, B.x - C.x) - a0
    while (d > Math.PI) d -= 2 * Math.PI
    while (d < -Math.PI) d += 2 * Math.PI
    const steps = Math.max(4, Math.round(Math.abs(d) / 0.2))
    const arc: Vec2[] = []
    for (let k = 0; k <= steps; k++) { const a = a0 + d * (k / steps); arc.push({ x: C.x + Math.cos(a) * R, y: C.y + Math.sin(a) * R }) }
    out = [...out.slice(0, i0), ...arc, ...out.slice(i1 + 1)]
  }
  return out
}

/** Deform a drawn wire polyline so it arcs around every node disc it crosses (but
    not the nodes it attaches to). Applied at PAINT time to every wire polyline. */
export function routeAroundNodes(pts: readonly Vec2[], discs: { c: Vec2; r: number }[]): readonly Vec2[] {
  let cur: readonly Vec2[] = pts
  for (const D of discs) cur = routeOne(cur, D.c, D.r)
  return cur
}

/** Existential dots: a dangling wire end is its own body (USER LAW — the loose
    end IS the first-order ∃, homed at the wire's scope); the ∀ via-body hub is
    the outermost point of that line of identity; a bare wire (no endpoints) is
    a dot alone. The dot is never invisible (a degenerate stub carrying the
    body position). */
export function existentialStubs(e: Engine): ExStub[] {
  const out: ExStub[] = []
  for (const [wid, w] of e.wires) {
    let dotId: string | null = null
    if (w.tipBodyId !== null) dotId = w.tipBodyId
    // a ∀ via-body hub (a first-class scope-homed body) is an ∃ dot
    else if (w.hub !== null && w.hub.kind === 'body') dotId = w.hub.bodyId
    if (dotId === null) continue
    const b = e.bodies.get(dotId)!
    out.push({ wid, from: b.pos, to: b.pos, dot: b.pos })
  }
  // bare (0-endpoint) wires carry no leg — just a scope-homed body (its dot IS
  // the whole rendering)
  for (const [wid, w] of Object.entries(e.d.wires)) {
    if (w.endpoints.length !== 0) continue
    const b = e.bodies.get(`j:${wid}`)
    if (b !== undefined) out.push({ wid, from: b.pos, to: b.pos, dot: b.pos })
  }
  return out
}
