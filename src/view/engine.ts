import type { Diagram, DiagramNode, NodeId, Port, RegionId, WireId } from '../kernel/diagram/diagram'
import { requiredPorts, portKey } from '../kernel/diagram/diagram'
import type { Vec2 } from './vec'
import { add } from './vec'
import type { NodeGeometry } from './bend'
import { bendGrid, atomGeometry } from './bend'
import { trompGrid } from './tromp'

/**
 * The converged render engine (round-8 lab spec). A Diagram-plus-boundary is
 * lifted into a set of relaxation BODIES — one per node, plus one JUNCTION body
 * for every branch (>=3-endpoint) line of identity — each carrying its local
 * anatomy geometry, its satellite constant discs, and an enclosing disc radius.
 * Positions/rotations are relaxed by `relax.ts`; geometry is emitted by
 * `wires.ts`/`paint.ts`. Nothing here is semantic and nothing is serialized.
 */

/** Standard named-disc radius (world units) — one size for every named disc. */
export const DISC_R = 5.5
/** Satellite stem length beyond the anatomy edge. */
export const SAT_STEM = 3.5
/** Sheet frame margin beyond the outermost region (world units). */
export const FRAME_MARGIN = 6

/** A constant leaf lifted OUT of the anatomy onto a short stem + named disc. */
export type Satellite = { readonly localPos: Vec2; readonly discLocal: Vec2; readonly label: string }

export type BodyKind = 'term' | 'ref' | 'atom' | 'junction'

export type Body = {
  readonly id: string
  readonly kind: BodyKind
  readonly node: DiagramNode | null
  readonly geometry: NodeGeometry | null
  /** Port key (pkey) -> anatomy-local anchor, ascale already folded in. */
  readonly localAnchor: Map<string, Vec2>
  readonly satellites: readonly Satellite[]
  readonly discR: number
  readonly region: RegionId
  pos: Vec2
  vel: Vec2
  theta: number
}

/** key null = the body's centre (junctions have no ports). */
export type LegEnd = { readonly body: string; readonly key: string | null }
export type Leg = { readonly wid: WireId; readonly from: LegEnd; readonly to: LegEnd }

export type RegionCircle = { center: Vec2; radius: number }

export type Engine = {
  readonly d: Diagram
  readonly bodies: Map<string, Body>
  readonly childrenOf: Map<RegionId, RegionId[]>
  /** node/junction body ids per region. */
  readonly membersOf: Map<RegionId, string[]>
  readonly legs: Leg[]
  /** boundary wire -> the body its frame exit emanates from. */
  readonly boundaryOf: Map<WireId, string>
  readonly boundary: readonly WireId[]
  regions: Map<RegionId, RegionCircle>
  /** relaxation tick counter (drives overlap-projection cadence, determinism). */
  tick: number
}

/** Local anatomy scale per node kind — atoms and terms are drawn larger so
    their structure is legible against the wire rhythm. */
export function ascaleOf(kind: BodyKind): number {
  return kind === 'atom' ? 2.0 : kind === 'term' ? 1.4 : 1
}

export function pkey(p: Port): string {
  return portKey(p)
}

/** The geometry of a diagram node: bent Tromp grid for terms, disc for atoms,
    named disc for refs. Moved here from the deleted scene layer. */
export function nodeGeometry(d: Diagram, id: NodeId): NodeGeometry {
  const n = d.nodes[id]
  if (n === undefined) throw new Error(`unknown node '${id}'`)
  switch (n.kind) {
    case 'term':
      return bendGrid(trompGrid(n.term))
    case 'atom': {
      const binder = d.regions[n.binder]!
      return atomGeometry(binder.kind === 'bubble' ? binder.arity : 0)
    }
    case 'ref':
      return atomGeometry(n.arity)
  }
}

/** World-space anchor of (geometry, centre, port). */
export function anchorOf(geometry: NodeGeometry, center: Vec2, port: Port): Vec2 {
  if (port.kind === 'output') return add(center, geometry.outputAnchor)
  const key = port.kind === 'freeVar' ? port.name : `a${port.index}`
  const local = geometry.portAnchors[key]
  if (local === undefined) throw new Error(`geometry has no anchor for port '${portKey(port)}'`)
  return add(center, local)
}

export function mkEngine(d: Diagram, boundary: readonly WireId[]): Engine {
  const bodies = new Map<string, Body>()
  let i = 0
  for (const [id, n] of Object.entries(d.nodes)) {
    const g = nodeGeometry(d, id)
    const localAnchor = new Map<string, Vec2>()
    let anatomyR = 3
    const ascale = ascaleOf(n.kind)
    for (const port of requiredPorts(d, n)) {
      const a0 = anchorOf(g, { x: 0, y: 0 }, port)
      const a = { x: a0.x * ascale, y: a0.y * ascale }
      localAnchor.set(pkey(port), a)
      anatomyR = Math.max(anatomyR, Math.hypot(a.x, a.y))
    }
    for (const arc of g.arcs) anatomyR = Math.max(anatomyR, arc.r)
    // satellites: constant leaves hang outside the anatomy on a stem, so
    // nothing paints over the term structure (geometry reserves the space).
    const satellites: Satellite[] = []
    if (n.kind === 'term') {
      for (const gl of g.glyphs) {
        const glr = Math.hypot(gl.pos.x, gl.pos.y)
        const dir = glr < 0.01 ? { x: 1, y: 0 } : { x: gl.pos.x / glr, y: gl.pos.y / glr }
        const discLocal = {
          x: gl.pos.x + dir.x * (anatomyR - glr + SAT_STEM + DISC_R),
          y: gl.pos.y + dir.y * (anatomyR - glr + SAT_STEM + DISC_R),
        }
        satellites.push({ localPos: gl.pos, discLocal, label: gl.constId })
      }
    }
    let discR = anatomyR + 2
    for (const s of satellites) {
      discR = Math.max(discR, Math.hypot(s.discLocal.x, s.discLocal.y) * (n.kind === 'term' ? 1.4 : 1) + DISC_R + 1.5)
    }
    if (n.kind === 'ref') discR = DISC_R + 1.5
    const ang = i * 2.399963, rad = 6 + 5 * i
    bodies.set(id, {
      id, kind: n.kind, node: n, geometry: g, localAnchor, satellites, discR,
      region: n.region,
      pos: { x: Math.cos(ang) * rad, y: Math.sin(ang) * rad }, vel: { x: 0, y: 0 }, theta: 0,
    })
    i++
  }

  const childrenOf = new Map<RegionId, RegionId[]>()
  const membersOf = new Map<RegionId, string[]>()
  for (const rid of Object.keys(d.regions)) { childrenOf.set(rid, []); membersOf.set(rid, []) }
  for (const [rid, r] of Object.entries(d.regions)) {
    if (r.kind !== 'sheet') childrenOf.get(r.parent)!.push(rid)
  }
  for (const [nid, n] of Object.entries(d.nodes)) membersOf.get(n.region)!.push(nid)

  const legs: Leg[] = []
  const boundaryOf = new Map<WireId, string>()
  const bset = new Set(boundary)
  for (const [wid, w] of Object.entries(d.wires)) {
    const ends = w.endpoints.map((ep): LegEnd => ({ body: ep.node, key: pkey(ep.port) }))
    const needsJunction = ends.length + (bset.has(wid) ? 1 : 0) >= 3
    if (needsJunction) {
      const jid = `j:${wid}`
      bodies.set(jid, {
        id: jid, kind: 'junction', node: null, geometry: null,
        localAnchor: new Map(), satellites: [], discR: 4.5, region: w.scope,
        pos: { x: (i++) * 3, y: -(i * 2) }, vel: { x: 0, y: 0 }, theta: 0,
      })
      membersOf.get(w.scope)!.push(jid)
      for (const en of ends) legs.push({ wid, from: en, to: { body: jid, key: null } })
      if (bset.has(wid)) boundaryOf.set(wid, jid)
    } else if (ends.length === 2) {
      legs.push({ wid, from: ends[0]!, to: ends[1]! })
    } else if (ends.length === 1) {
      if (bset.has(wid)) boundaryOf.set(wid, ends[0]!.body)
      else legs.push({ wid, from: ends[0]!, to: ends[0]! }) // genuine exists loose end -> stub
    }
  }
  return { d, bodies, childrenOf, membersOf, legs, boundaryOf, boundary, regions: new Map(), tick: 0 }
}

/** Map an anatomy-local point (before ascale) into world space through the
    body's scale, rotation, and position. Shared by paint and hit-testing. */
export function localToWorld(b: Body, lp: Vec2): Vec2 {
  const ascale = ascaleOf(b.kind)
  const c = Math.cos(b.theta), s = Math.sin(b.theta)
  const x = lp.x * ascale, y = lp.y * ascale
  return { x: b.pos.x + x * c - y * s, y: b.pos.y + x * s + y * c }
}

/** Satellite discs are slightly smaller than relation-ref discs. */
export const SAT_DISC_R = DISC_R * 0.82

/** World centre of a satellite's named disc. */
export function satelliteWorld(b: Body, sat: Satellite): Vec2 {
  return localToWorld(b, sat.discLocal)
}

/** World anchor of (body, port key); key null returns the body centre. */
export function worldAnchor(b: Body, key: string | null): Vec2 {
  if (key === null) return b.pos
  const a = b.localAnchor.get(key)!
  const c = Math.cos(b.theta), s = Math.sin(b.theta)
  return { x: b.pos.x + a.x * c - a.y * s, y: b.pos.y + a.x * s + a.y * c }
}

/** The outward normal at (body, port key), in world radians. Junctions have no
    ports, so their "normal" is the direction toward the far endpoint. */
export function portNormal(b: Body, key: string | null, toward: Vec2): number {
  if (key === null) return Math.atan2(toward.y - b.pos.y, toward.x - b.pos.x)
  const a = b.localAnchor.get(key)!
  return Math.atan2(a.y, a.x) + b.theta
}

/** The sheet frame box (sheet region radius + margin). Null before the first
    settle populates region circles. */
export function frameBounds(e: Engine): { minX: number; maxX: number; minY: number; maxY: number; frameR: number; center: Vec2 } | null {
  const sheet = e.regions.get(e.d.root)
  if (sheet === undefined) return null
  const frameR = sheet.radius + FRAME_MARGIN
  return {
    minX: sheet.center.x - frameR, maxX: sheet.center.x + frameR,
    minY: sheet.center.y - frameR, maxY: sheet.center.y + frameR,
    frameR, center: sheet.center,
  }
}
