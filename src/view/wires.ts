import type { WireId } from '../kernel/diagram/diagram'
import type { Vec2 } from './vec'
import type { Engine, Leg, LegEnd, WireView } from './engine'
import { ROUTE_CLEAR, routeObstacles, routeBounds, wireTerminalBCs, wireTerminalPoints } from './engine'
import { mkFreeSpace, route, type FreeSpace } from './route/freespace'
import { edgeCurvePts } from './route/curve'

/**
 * Wire geometry over the ROUTED NETWORK (USER ruling 2026-07-24), pure —
 * returns traced polylines, paints nothing. Each drawn stroke IS the
 * rod-energy curve: the deterministic Hermite curve through the edge's route
 * waypoints with the terminal boundary conditions (clamped port/slot normals,
 * natural junction/dot ends — see route/curve.ts). The renderer draws exactly
 * what the energy charges; there is no separate rounding pass.
 */

export type LegGeom = { leg: Leg; pts: Vec2[] }
export type ExStub = { wid: WireId; from: Vec2; to: Vec2; dot: Vec2 }

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

/** Exact rendering-state key: legs depend on body poses (obstacles +
    terminals), wire nets, and the frame/scale. Building the key is microseconds
    against a ~10 ms re-route of a large scene, so resting frames render from
    cache. */
function legsKey(e: Engine): string {
  const parts: (string | number)[] = [e.scale, e.slotShift, e.frame === null ? 'nf' : `${e.frame.center.x},${e.frame.center.y},${e.frame.half}`]
  for (const [id, b] of e.bodies) parts.push(id, b.pos.x, b.pos.y, b.theta)
  for (const [wid, w] of e.wires) {
    parts.push(wid)
    for (const p of w.net.junctions) parts.push(p.x, p.y)
    for (const [u, v] of w.net.edges) parts.push(u, v)
  }
  return parts.join(',')
}

const legsCache = new WeakMap<Engine, { key: string; legs: LegGeom[] }>()

/** Every drawable stroke as its rod-energy curve samples. The result is
    CACHED against the exact rendering state — callers must treat it as
    immutable. */
export function computeLegs(e: Engine): LegGeom[] {
  const key = legsKey(e)
  const hit = legsCache.get(e)
  if (hit !== undefined && hit.key === key) return hit.legs
  const legs = computeLegsUncached(e)
  legsCache.set(e, { key, legs })
  return legs
}

function computeLegsUncached(e: Engine): LegGeom[] {
  const fs: FreeSpace = mkFreeSpace(routeObstacles(e), routeBounds(e))
  const out: LegGeom[] = []
  for (const [wid, w] of e.wires) {
    const terms = wireTerminalPoints(e, w)
    const bcs = wireTerminalBCs(e, w)
    const pos = (v: number): Vec2 => (v < terms.length ? terms[v]! : w.net.junctions[v - terms.length]!)
    for (const [u, v] of w.net.edges) {
      const rt = route(fs, pos(u), pos(v))
      const pts = edgeCurvePts(u < bcs.length ? bcs[u]! : null, v < bcs.length ? bcs[v]! : null, rt.pts, ROUTE_CLEAR * e.scale)
      out.push({ leg: { wid, from: endId(wid, w, u), to: endId(wid, w, v) }, pts })
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
