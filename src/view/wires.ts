import type { WireId } from '../kernel/diagram/diagram'
import type { Vec2 } from './vec'
import type { Engine, Leg, LegEnd, WireLegEnd, WireView } from './engine'
import { frameBounds, frameSlots, resolveLeg, traceLeg } from './engine'

/**
 * Wire geometry over the PLAN-22 massless elastica, pure — returns traced
 * polylines, paints nothing. Each leg IS the minimum-energy θ-quadratic
 * interpolant of its live boundary data (elastica.ts); rendering simply traces
 * it at paint resolution (n=30). Loops and kinks are unrepresentable, so the
 * traced line is always a smooth non-self-crossing curve leaving each port
 * perpendicular by construction. A boundary wire's legs reach its slot-attracted
 * exit hub; boundaryExits adds the short exit→slot connector and the frame tick.
 * ∃/∀ ends and bare wires become existential dots.
 */

/** Trace resolution for painted legs (segments per leg). */
const PAINT_N = 30

export type LegGeom = { leg: Leg; pts: Vec2[] }
export type BoundaryExit = { wid: WireId; pts: Vec2[]; tick: { center: Vec2; angle: number } }
export type ExStub = { wid: WireId; from: Vec2; to: Vec2; dot: Vec2 }

/** The rendering identity of a leg terminal: real (body, key) at a port bind
    and the ∀ via-body hub; a wire-local id for a pure hub point, the boundary
    exit point, or the ∃ tip body. Endpoint-level gestures (drag-join) read
    these. */
function endId(wid: WireId, w: WireView, end: WireLegEnd): LegEnd {
  switch (end.kind) {
    case 'bind': return { body: w.binds[end.i]!.body, key: w.binds[end.i]!.key }
    case 'tip': return { body: w.tipBodyId!, key: null }
    case 'exit': return { body: `w:${wid}:exit`, key: null }
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

/** Traced polyline for every leg (boundary legs included — they reach the exit
    hub, and their frame connector is a boundaryExit). */
export function legPaths(e: Engine): { wid: WireId; pts: Vec2[] }[] {
  return computeLegs(e).map((g) => ({ wid: g.leg.wid, pts: g.pts }))
}

/** One frame exit per boundary wire: the connector from the wire's exit point
    (which the physics parks AT the slot) out to its canonical perimeter slot
    (fixed in boundary order, clockwise from the frame pip), meeting the frame
    along the slot normal, plus the perpendicular frame tick. Drawn even mid-
    transient so the painted boundary wire is structurally gapless — the exit
    leg reaches the exit point, this connector carries it the rest of the way. */
export function boundaryExits(e: Engine): BoundaryExit[] {
  const fbb = frameBounds(e)
  if (fbb === null) return []
  const slots = frameSlots(fbb, e.boundary.length)
  const out: BoundaryExit[] = []
  for (const [wid, w] of e.wires) {
    if (w.slot === null || w.exit === null) continue
    const slot = slots[w.slot]
    if (slot === undefined) continue
    // a short quadratic from the exit point into the slot along the slot normal
    // (a straight join at rest when the exit sits at the slot; a smooth
    // perpendicular meeting under transient offset)
    const ex = w.exit.pos, sp = slot.point
    const handle = Math.hypot(sp.x - ex.x, sp.y - ex.y) * 0.5
    const cx = sp.x + Math.cos(slot.normal) * handle, cy = sp.y + Math.sin(slot.normal) * handle
    const pts: Vec2[] = []
    for (let k = 0; k <= 8; k++) {
      const t = k / 8, u = 1 - t
      pts.push({ x: u * u * ex.x + 2 * u * t * cx + t * t * sp.x, y: u * u * ex.y + 2 * u * t * cy + t * t * sp.y })
    }
    out.push({ wid, pts, tick: { center: sp, angle: slot.normal + Math.PI / 2 } })
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
