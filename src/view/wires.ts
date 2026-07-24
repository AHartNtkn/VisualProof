import type { WireId } from '../kernel/diagram/diagram'
import type { Vec2 } from './vec'
import type { Engine, Leg, LegEnd, WireView } from './engine'
import { escapePoint, routeObstacles, routeBounds, slotEscape, wireTerminalPoints } from './engine'
import { mkFreeSpace, route, type FreeSpace } from './route/freespace'

/**
 * Wire geometry over the ROUTED NETWORK (USER ruling 2026-07-24), pure —
 * returns traced polylines, paints nothing. Each drawn stroke is a routed
 * shortest path through free space (node discs are hard obstacles), FILLETED
 * at its interior corners as a RENDERER operation: the rounding selects no
 * winding basins and stores no state — it is a local corner treatment of the
 * already-clear route corridor. A port stroke begins with the fixed escape
 * stub (rim anchor → escape point), so exits are perpendicular by
 * construction.
 */

/** Fillet radius (world units, scaled by content fill) and samples/corner. */
const FILLET_R = 2.0
const FILLET_N = 6

export type LegGeom = { leg: Leg; pts: Vec2[] }
export type ExStub = { wid: WireId; from: Vec2; to: Vec2; dot: Vec2 }

/** Round the interior corners of a polyline with quadratic fillets clipped to
    the shorter adjacent half-segment. Endpoints are preserved exactly. */
export function filletPolyline(pts0: readonly Vec2[], r: number): Vec2[] {
  // drop degenerate consecutive duplicates first (stub joins, collinear routes)
  const pts: Vec2[] = []
  for (const p of pts0) {
    const last = pts[pts.length - 1]
    if (last !== undefined && Math.hypot(p.x - last.x, p.y - last.y) < 1e-9) continue
    pts.push(p)
  }
  if (pts.length <= 2) return pts
  const out: Vec2[] = [pts[0]!]
  for (let i = 1; i + 1 < pts.length; i++) {
    const a = pts[i - 1]!, b = pts[i]!, c = pts[i + 1]!
    const d1 = Math.hypot(b.x - a.x, b.y - a.y), d2 = Math.hypot(c.x - b.x, c.y - b.y)
    const t = Math.min(r, d1 / 2, d2 / 2)
    if (t < 1e-9) { out.push(b); continue }
    const p = { x: b.x + ((a.x - b.x) / d1) * t, y: b.y + ((a.y - b.y) / d1) * t }
    const q = { x: b.x + ((c.x - b.x) / d2) * t, y: b.y + ((c.y - b.y) / d2) * t }
    for (let k = 0; k <= FILLET_N; k++) {
      const u = k / FILLET_N
      const v = 1 - u
      const np = {
        x: v * v * p.x + 2 * v * u * b.x + u * u * q.x,
        y: v * v * p.y + 2 * v * u * b.y + u * u * q.y,
      }
      const last = out[out.length - 1]!
      if (Math.hypot(np.x - last.x, np.y - last.y) < 1e-9) continue
      out.push(np)
    }
  }
  out.push(pts[pts.length - 1]!)
  return out
}

/** The rendering identity of a network vertex: real (body, key) at a port
    bind and the wire-owned END body; a wire-local id for a boundary slot or a
    junction vertex. Endpoint-level gestures (drag-join) read these. */
function endId(wid: WireId, w: WireView, v: number): LegEnd {
  const nB = w.binds.length
  const nS = w.slots.length
  if (v < nB) return { body: w.binds[v]!.body, key: w.binds[v]!.key }
  if (v < nB + nS) return { body: `w:${wid}:slot:${w.slots[v - nB]!}`, key: null }
  if (w.endBodyId !== null && v === nB + nS) return { body: w.endBodyId, key: null }
  return { body: `w:${wid}:j${v - nB - nS - (w.endBodyId !== null ? 1 : 0)}`, key: null }
}

/** Every drawable stroke as a filleted routed polyline. A port-incident edge
    is prefixed with its fixed escape stub so the drawn stroke starts ON the
    rim heading along the port normal. */
export function computeLegs(e: Engine): LegGeom[] {
  const fs: FreeSpace = mkFreeSpace(routeObstacles(e), routeBounds(e))
  const out: LegGeom[] = []
  const r = FILLET_R * e.scale
  for (const [wid, w] of e.wires) {
    const terms = wireTerminalPoints(e, w)
    const pos = (v: number): Vec2 => (v < terms.length ? terms[v]! : w.net.junctions[v - terms.length]!)
    for (const [u, v] of w.net.edges) {
      const rt = route(fs, pos(u), pos(v))
      let pts: Vec2[] = [...rt.pts]
      // prepend/append the fixed stubs: port rim anchors and frame-slot points
      // (perpendicular exits/arrivals BY CONSTRUCTION)
      const nB = w.binds.length
      const stubEnd = (vv: number): Vec2 | null => {
        if (vv < nB) return escapePoint(e, w.binds[vv]!).anchor
        if (vv < nB + w.slots.length) return slotEscape(e, w.slots[vv - nB]!)?.point ?? null
        return null
      }
      const su = stubEnd(u), sv = stubEnd(v)
      if (su !== null) pts = [su, ...pts]
      if (sv !== null) pts = [...pts, sv]
      out.push({ leg: { wid, from: endId(wid, w, u), to: endId(wid, w, v) }, pts: filletPolyline(pts, r) })
    }
  }
  return out
}

/** Traced polyline for every stroke (boundary edges included). */
export function legPaths(e: Engine): { wid: WireId; pts: Vec2[] }[] {
  return computeLegs(e).map((g) => ({ wid: g.leg.wid, pts: g.pts }))
}

/** Quantifier dots: a dangling wire end is its own body (USER LAW — the loose
    end IS the first-order ∃, homed at the wire's scope); the ∀ via body is the
    outermost point of that line of identity; a bare wire (no endpoints) is a dot
    alone. Every wire-owned END body is dotted at its position. */
export function existentialStubs(e: Engine): ExStub[] {
  const out: ExStub[] = []
  for (const [wid, w] of e.wires) {
    if (w.endBodyId === null) continue
    const b = e.bodies.get(w.endBodyId)!
    out.push({ wid, from: b.pos, to: b.pos, dot: b.pos })
  }
  // bare (0-endpoint) wires carry no edges — just a scope-homed body (its dot
  // IS the whole rendering)
  for (const [wid, w] of Object.entries(e.d.wires)) {
    if (w.endpoints.length !== 0) continue
    const b = e.bodies.get(`j:${wid}`)
    if (b !== undefined) out.push({ wid, from: b.pos, to: b.pos, dot: b.pos })
  }
  return out
}
