import type { Diagram, DiagramNode, NodeId, Port, RegionId, WireId } from '../kernel/diagram/diagram'
import { requiredPorts, portKey } from '../kernel/diagram/diagram'
import { deepestCommonAncestor } from '../kernel/diagram/regions'
import type { Vec2 } from './vec'
import { add } from './vec'
import type { NodeGeometry } from './bend'
import { bendGrid, atomGeometry } from './bend'
import { trompGrid } from './tromp'
import type { WireChain } from './wirechain'
import { mkChain, PITCH } from './wirechain'

/**
 * The converged render engine (round-8 lab spec). A Diagram-plus-boundary is
 * lifted into a set of relaxation BODIES — one per node, plus one JUNCTION body
 * for every branch (>=3-endpoint) line of identity — each carrying its local
 * anatomy geometry and an enclosing disc radius. Positions/rotations are
 * relaxed by `relax.ts`; geometry is emitted by `wires.ts`/`paint.ts`. Nothing
 * here is semantic and nothing is serialized.
 */

/** Standard named-disc radius (world units) — one size for every named disc. */
export const DISC_R = 5.5
/** Sheet frame margin beyond the outermost region (world units). */
export const FRAME_MARGIN = 6
/** Corner radius of the sheet frame, world units — shared by the drawn
    rounded rectangle and the boundary-exit geometry so exits ride the
    visible frame line exactly. */
export const FRAME_CORNER_W = 8

export type BodyKind = 'term' | 'ref' | 'atom' | 'junction' | 'anchor'

export type Body = {
  readonly id: string
  readonly kind: BodyKind
  readonly node: DiagramNode | null
  readonly geometry: NodeGeometry | null
  /** Port key (pkey) -> anatomy-local anchor, ascale already folded in. */
  readonly localAnchor: Map<string, Vec2>
  readonly discR: number
  readonly region: RegionId
  pos: Vec2
  vel: Vec2
  theta: number
}

/** key null = the body's centre (junctions have no ports). */
export type LegEnd = { readonly body: string; readonly key: string | null }
export type Leg = { readonly wid: WireId; readonly from: LegEnd; readonly to: LegEnd }

/** A region's drawn circle. `support` lists the direct items (member body or
    child region) ON the rim — the only content the circle's geometry depends
    on, and therefore where region-level forces land. */
export type RegionCircle = { center: Vec2; radius: number; support: readonly { mid?: string; sub?: RegionId }[] }

export type Engine = {
  readonly d: Diagram
  readonly bodies: Map<string, Body>
  readonly childrenOf: Map<RegionId, RegionId[]>
  /** node/junction body ids per region. */
  readonly membersOf: Map<RegionId, string[]>
  /** PLAN 21: each wire is a physical CHAIN (a tree for multiport wires) —
      see wirechain.ts for the energy model. Replaces legs + hub bodies. */
  readonly chains: Map<WireId, WireChain>
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

/** All bodies of a region subtree: the subtree's mass in projections and the
    grab set of a region drag. Every region carries at least one body — empty
    leaf regions get an invisible anchor body at mkEngine, so bodies are the
    ONLY kind of positional state. */
export function subtreeCarriers(e: Engine, rid: RegionId): string[] {
  const out = [...e.membersOf.get(rid)!]
  for (const c of e.childrenOf.get(rid)!) out.push(...subtreeCarriers(e, c))
  return out
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
    const discR = n.kind === 'ref' ? DISC_R + 1.5 : anatomyR + 2
    const ang = i * 2.399963, rad = 6 + 5 * i
    bodies.set(id, {
      id, kind: n.kind, node: n, geometry: g, localAnchor, discR,
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

  // Empty leaf regions get an invisible anchor body: the region's positional
  // state carrier. With it, cohesion/repulsion/damping/projection apply to
  // empty cuts uniformly — without it they are dynamically inert (only
  // projections could teleport them, nothing could restore them, and one
  // dangling empty cut inflates its parent circle into permanent violation).
  // discR restores the historical empty-region circle radius of 10 once
  // recomputeRegions adds REGION_PAD around the disc.
  for (const [rid] of Object.entries(d.regions)) {
    if (membersOf.get(rid)!.length === 0 && childrenOf.get(rid)!.length === 0) {
      const aid = `anchor:${rid}`
      const ang = i * 2.399963, rad = 6 + 5 * i
      bodies.set(aid, {
        id: aid, kind: 'anchor', node: null, geometry: null,
        localAnchor: new Map(), discR: 5, region: rid,
        pos: { x: Math.cos(ang) * rad, y: Math.sin(ang) * rad }, vel: { x: 0, y: 0 }, theta: 0,
      })
      membersOf.get(rid)!.push(aid)
      i++
    }
  }

  const chains = new Map<WireId, WireChain>()
  const bset = new Set(boundary)
  const slotOf = new Map(boundary.map((w, k) => [w, k] as const))
  for (const [wid, w] of Object.entries(d.wires)) {
    const ends = w.endpoints.map((ep): LegEnd => ({ body: ep.node, key: pkey(ep.port) }))
    // The line's OUTERMOST POINT is where its individual is quantified, and
    // it must be a body homed at the wire's SCOPE (USER LAW: dangling ends
    // are their own nodes — the ∃ is manipulable independently of what it
    // attaches to). A dangling wire's free chain end IS that body. When the
    // scope sits ABOVE the dca (the ∀ shape) a dangling branch reaches a
    // scope-homed body, so the line never contorts through its scope.
    // Boundary wires get a frame-slot terminal instead of an ∃ end.
    const isBoundary = bset.has(wid)
    const mkWireBody = (id: string, region: RegionId, near?: Vec2): Body => {
      // seed NEAR the wire's own anchors, not on the global spiral: after a
      // rewrite, spiral-seeded ends left wires stretched wildly across the
      // sheet (USER report)
      const seed = near !== undefined
        ? { x: near.x + 4 + (i % 3), y: near.y - 3 - (i % 2) }
        : { x: (i++) * 3, y: -(i * 2) }
      i++
      const b: Body = {
        id, kind: 'junction', node: null, geometry: null,
        localAnchor: new Map(), discR: 4.5, region,
        pos: seed, vel: { x: 0, y: 0 }, theta: 0,
      }
      bodies.set(id, b)
      membersOf.get(region)!.push(id)
      return b
    }
    if (ends.length === 0) {
      // a bare ∃ — the wire asserts only that an individual exists: one
      // scope-homed body, no chain (its dot is the whole rendering)
      mkWireBody(`j:${wid}`, w.scope)
      continue
    }
    // terminals: port anchors first (in endpoint order), then homed/slot ends
    const terminalPos: Vec2[] = ends.map((en) => worldBindAnchor(bodies.get(en.body)!, en.key!))
    const binds = ends.map((en, k) => ({ idx: k, body: en.body, key: en.key! }))
    const homed: { idx: number; bodyId: string }[] = []
    const slots: { idx: number; slot: number }[] = []
    const dca = w.endpoints
      .map((ep) => d.nodes[ep.node]!.region)
      .reduce((a, b) => deepestCommonAncestor(d, a, b))
    if (isBoundary) {
      // slot position is derived per tick; seed near the first anchor
      slots.push({ idx: terminalPos.length, slot: slotOf.get(wid)! })
      terminalPos.push({ x: terminalPos[0]!.x, y: terminalPos[0]!.y - 6 })
    } else if (ends.length === 1) {
      const b = mkWireBody(`j:${wid}`, w.scope, terminalPos[0])
      homed.push({ idx: terminalPos.length, bodyId: b.id })
      terminalPos.push(b.pos)
    } else if (w.scope !== dca) {
      const cx = terminalPos.reduce((s, p) => s + p.x, 0) / terminalPos.length
      const cy = terminalPos.reduce((s, p) => s + p.y, 0) / terminalPos.length
      const b = mkWireBody(`x:${wid}`, w.scope, { x: cx, y: cy })
      homed.push({ idx: terminalPos.length, bodyId: b.id })
      terminalPos.push(b.pos)
    }
    const built = mkChain(terminalPos, PITCH)
    chains.set(wid, { pts: built.pts, adj: built.adj, binds, homed, slots, pitch: PITCH })
  }

  return { d, bodies, childrenOf, membersOf, chains, boundary, regions: new Map(), tick: 0 }
}

/**
 * Transplant the physics state of every body shared between two engines. When a
 * new engine is built for the next diagram in a replay, bodies whose id survives
 * (nodes keyed by NodeId, junctions by `j:<wireId>`) keep their pos/vel/theta so
 * the layout glides from where it was rather than re-seeding from the spiral.
 * Bodies present only in `next` keep their deterministic mkEngine seeds. Vec2 is
 * treated as an immutable value here, matching relax.ts's replace-not-mutate
 * discipline, so copying the reference cannot alias `prev` into `next`'s motion.
 */
export function carryOver(prev: Engine, next: Engine): void {
  for (const [id, nb] of next.bodies) {
    const pb = prev.bodies.get(id)
    if (pb === undefined) continue
    nb.pos = pb.pos
    nb.vel = pb.vel
    nb.theta = pb.theta
  }
  // chains glide too: a surviving wire with the same terminal signature
  // keeps its relaxed shape (pts/adj) instead of re-seeding a star
  for (const [wid, nc] of next.chains) {
    const pc = prev.chains.get(wid)
    if (pc === undefined) continue
    const sig = (c: WireChain): string =>
      [...c.binds.map((b) => `${b.body}:${b.key}`), `h${c.homed.length}`, `s${c.slots.length}`].join('|')
    if (sig(pc) !== sig(nc)) continue
    nc.pts = pc.pts.map((p) => ({ ...p }))
    nc.adj = pc.adj.map((a) => [...a])
    nc.binds = pc.binds.map((b) => ({ ...b }))
    nc.homed = pc.homed.map((h) => ({ ...h }))
    nc.slots = pc.slots.map((s) => ({ ...s }))
  }
}

/** Map an anatomy-local point (before ascale) into world space through the
    body's scale, rotation, and position. Shared by paint and hit-testing. */
export function localToWorld(b: Body, lp: Vec2): Vec2 {
  const ascale = ascaleOf(b.kind)
  const c = Math.cos(b.theta), s = Math.sin(b.theta)
  const x = lp.x * ascale, y = lp.y * ascale
  return { x: b.pos.x + x * c - y * s, y: b.pos.y + x * s + y * c }
}

/** World anchor of (body, port key); key null returns the body centre. */
export function worldAnchor(b: Body, key: string | null): Vec2 {
  if (key === null) return b.pos
  const a = b.localAnchor.get(key)!
  const c = Math.cos(b.theta), s = Math.sin(b.theta)
  return { x: b.pos.x + a.x * c - a.y * s, y: b.pos.y + a.x * s + a.y * c }
}

/** Where a WIRE attaches to a body: the point on the DISC EDGE in the
    port's direction. The interior anchor is node anatomy (the port dot);
    a wire pinned there begins inside the node and must escape the disc
    through a corridor that exempts a swath of it (USER report: edges
    beginning on the interior, exiting at non-perpendicular angles). The
    edge attachment makes the perpendicular exit a boundary condition. */
export function worldBindAnchor(b: Body, key: string): Vec2 {
  const a = b.localAnchor.get(key)!
  const la = Math.hypot(a.x, a.y)
  const ux = la < 1e-9 ? 1 : a.x / la, uy = la < 1e-9 ? 0 : a.y / la
  const c = Math.cos(b.theta), s = Math.sin(b.theta)
  return {
    x: b.pos.x + (ux * c - uy * s) * b.discR,
    y: b.pos.y + (ux * s + uy * c) * b.discR,
  }
}

/** The outward normal at (body, port key), in world radians. Junctions have no
    ports, so their "normal" is the direction toward the far endpoint. */
export function portNormal(b: Body, key: string | null, toward: Vec2): number {
  if (key === null) return Math.atan2(toward.y - b.pos.y, toward.x - b.pos.x)
  const a = b.localAnchor.get(key)!
  return Math.atan2(a.y, a.x) + b.theta
}

export type FrameBounds = { minX: number; maxX: number; minY: number; maxY: number; frameR: number; center: Vec2 }

/** The sheet frame box (sheet region radius + margin). Null before the first
    settle populates region circles. */
export function frameBounds(e: Engine): FrameBounds | null {
  const sheet = e.regions.get(e.d.root)
  if (sheet === undefined) return null
  const frameR = sheet.radius + FRAME_MARGIN
  return {
    minX: sheet.center.x - frameR, maxX: sheet.center.x + frameR,
    minY: sheet.center.y - frameR, maxY: sheet.center.y + frameR,
    frameR, center: sheet.center,
  }
}

/** A boundary slot: a fixed perimeter point plus the outward frame normal there. */
export type FrameSlot = { readonly point: Vec2; readonly normal: number }

/**
 * The n boundary slots: points spaced evenly BY ARC LENGTH around the frame's
 * rounded-rectangle perimeter, slot 0 at the top-edge midpoint (the pip origin)
 * and proceeding CLOCKWISE (canvas y-down). `normal` is the outward frame normal
 * — axis-aligned on a straight edge, radial from the corner centre on a corner
 * (the same rounded rect paint draws, so a slot rides the visible frame line).
 * Slot i is the fixed frame-relative target of boundary wire i, so exits carry
 * the boundary order and structurally cannot swap.
 */
export function frameSlots(fb: FrameBounds, n: number): FrameSlot[] {
  const cx = fb.center.x, cy = fb.center.y
  const hw = (fb.maxX - fb.minX) / 2, hh = (fb.maxY - fb.minY) / 2
  const r = Math.min(FRAME_CORNER_W, hw, hh)
  const sx = hw - r, sy = hh - r
  const arc = (Math.PI / 2) * r
  const corner = (ccx: number, ccy: number, phi: number): FrameSlot =>
    ({ point: { x: ccx + Math.cos(phi) * r, y: ccy + Math.sin(phi) * r }, normal: phi })
  // Perimeter segments, clockwise from the top-edge midpoint. `u` is arc length
  // from the segment start; corner arcs advance the angle by u / r.
  const segs: { len: number; at: (u: number) => FrameSlot }[] = [
    { len: sx, at: (u) => ({ point: { x: cx + u, y: cy - hh }, normal: -Math.PI / 2 }) },
    { len: arc, at: (u) => corner(cx + sx, cy - sy, -Math.PI / 2 + u / r) },
    { len: 2 * sy, at: (u) => ({ point: { x: cx + hw, y: cy - sy + u }, normal: 0 }) },
    { len: arc, at: (u) => corner(cx + sx, cy + sy, u / r) },
    { len: 2 * sx, at: (u) => ({ point: { x: cx + sx - u, y: cy + hh }, normal: Math.PI / 2 }) },
    { len: arc, at: (u) => corner(cx - sx, cy + sy, Math.PI / 2 + u / r) },
    { len: 2 * sy, at: (u) => ({ point: { x: cx - hw, y: cy + sy - u }, normal: Math.PI }) },
    { len: arc, at: (u) => corner(cx - sx, cy - sy, Math.PI + u / r) },
    { len: sx, at: (u) => ({ point: { x: cx - sx + u, y: cy - hh }, normal: -Math.PI / 2 }) },
  ]
  const P = segs.reduce((s, g) => s + g.len, 0)
  const slotAt = (s0: number): FrameSlot => {
    let s = ((s0 % P) + P) % P
    for (const g of segs) {
      if (s < g.len) return g.at(s)
      s -= g.len
    }
    const last = segs[segs.length - 1]!
    return last.at(last.len)
  }
  const out: FrameSlot[] = []
  for (let i = 0; i < n; i++) out.push(slotAt((i / n) * P))
  return out
}
