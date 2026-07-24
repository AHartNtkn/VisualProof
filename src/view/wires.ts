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

/** The rendering identity of a leg terminal: real (body, key) at a port bind and
    the wire-owned END body (∃ tip / ∀ via); a wire-local id for a boundary slot or
    a Steiner branch vertex. Endpoint-level gestures (drag-join) read these. */
function endId(wid: WireId, w: WireView, end: WireLegEnd): LegEnd {
  switch (end.kind) {
    case 'bind': return { body: w.binds[end.i]!.body, key: w.binds[end.i]!.key }
    case 'end': return { body: w.endBodyId!, key: null }
    case 'slot': return { body: `w:${wid}:slot:${w.slots[end.i]!}`, key: null }
    case 'branch': return { body: `w:${wid}:b${end.i}`, key: null }
  }
}

/** Every drawable leg as a traced polyline. The traced curve is the wire — it
    starts ON the rim heading along the port normal and closes on its far end
    (another port, a Steiner branch vertex, a fixed boundary slot, or the
    wire's own END body — the ∃ tip / ∀ via), tangent range <= pi so it
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

/** Quantifier dots: a dangling wire end is its own body (USER LAW — the loose
    end IS the first-order ∃, homed at the wire's scope); the ∀ via body is the
    outermost point of that line of identity; a bare wire (no endpoints) is a dot
    alone. Every wire-owned END body is dotted at its position (a degenerate stub
    carrying the body position). */
export function existentialStubs(e: Engine): ExStub[] {
  const out: ExStub[] = []
  for (const [wid, w] of e.wires) {
    if (w.endBodyId === null) continue
    const b = e.bodies.get(w.endBodyId)!
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
