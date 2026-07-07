import type { WireId } from '../kernel/diagram/diagram'
import type { Vec2 } from './vec'
import type { Engine, Leg, LegEnd, WireLegEnd, WireView } from './engine'
import { resolveLeg, traceLeg } from './engine'

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

/** The world position of every INTERIOR wire-owned branch HUB POINT (plan 24: an
    interior k-ary junction) — these carry a drawn junction dot (a dot appears at a
    genuine interior branch, never on a plain 2-point wire). A BOUNDARY wire's hub
    (slot !== null) is EXCLUDED: no visible node/dot ever appears at a boundary
    attachment, including a k≥2 boundary wire's hub (USER RULING 2026-07-07). (A ∀
    via-body / ∃ tip is a first-class body, drawn by existentialStubs.) */
export function hubPoints(e: Engine): { wid: WireId; pos: Vec2 }[] {
  const out: { wid: WireId; pos: Vec2 }[] = []
  for (const [wid, w] of e.wires) {
    if (w.hub !== null && w.hub.kind === 'point' && w.slot === null) out.push({ wid, pos: w.hub.pos })
  }
  return out
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
