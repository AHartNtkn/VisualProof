import type { Diagram, DiagramNode, NodeId, Port, RegionId, WireId } from '../kernel/diagram/diagram'
import { requiredPorts, portKey } from '../kernel/diagram/diagram'
import { deepestCommonAncestor } from '../kernel/diagram/regions'
import type { Vec2 } from './vec'
import { add } from './vec'
import type { NodeGeometry } from './bend'
import { bendGrid, atomGeometry } from './bend'
import { trompGrid } from './tromp'
import type { LegCache, Sol } from './elastica'
import { mkLegCache, solveLeg, closeAt, trace, QN, WELL_S } from './elastica'

/**
 * The converged render engine (round-8 lab spec). A Diagram-plus-boundary is
 * lifted into a set of relaxation BODIES — one per node, plus one JUNCTION body
 * for every branch (>=3-endpoint) line of identity — each carrying its local
 * anatomy geometry and an enclosing disc radius. Positions/rotations are
 * relaxed by `relax.ts`; geometry is emitted by `wires.ts`/`paint.ts`. Nothing
 * here is semantic and nothing is serialized.
 *
 * PLAN 22: wires are MASSLESS ELASTICA (see elastica.ts). A wire has no shape
 * state — each leg is the minimum-energy theta-quadratic interpolant of its
 * CURRENT boundary data, recomputed per evaluation and memoized on the exact
 * boundary tuple. The only wire DOF are the branch hub (a wire-owned point,
 * or the ∀ body) and the per-leg arrival angles; ∃/∀ ends stay first-class
 * bodies. Loops and kinks are UNREPRESENTABLE (tangent range <= pi).
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
  theta: number
}

/** key null = the body's centre (junctions have no ports). */
export type LegEnd = { readonly body: string; readonly key: string | null }
export type Leg = { readonly wid: WireId; readonly from: LegEnd; readonly to: LegEnd }

// ---- the massless-elastica wire view-state (plan 22) -----------------------

/** A wire endpoint bound to a node port (the disc-edge rim anchor + the port
    normal are DERIVED from the body each evaluation — never stored). */
export type WireBind = { readonly body: string; readonly key: string }

/** A leg terminal. `bind i` = binds[i] (port rim + normal); `tip` = the ∃ free
    end (a body); `hub` = the branch point (a wire-owned point, the ∀ body, or a
    boundary wire's slot-attracted exit body), reached along the leg's arrival
    angle. Every leg starts at a `bind`. */
export type WireLegEnd =
  | { readonly kind: 'bind'; readonly i: number }
  | { readonly kind: 'tip' }
  | { readonly kind: 'hub' }

/** One leg of a wire: the massless θ-quadratic from terminal `a` (a port bind,
    exiting along its normal) to terminal `b` (hub / another bind / ∃ tip /
    boundary exit). `hubAngle` is the arrival DIRECTION at a hub end (a wire
    DOF descended by the gated step); `cache` memoizes the solve on the exact
    boundary tuple. */
export type WireLeg = {
  readonly a: WireLegEnd
  readonly b: WireLegEnd
  hubAngle: number
  readonly cache: LegCache
}

/** The branch point of a k-ary wire: a wire-owned relaxation POINT (pure
    junction), or the homed ∀ body (the via-body shape). */
export type WireHub =
  | { readonly kind: 'point'; pos: Vec2 }
  | { readonly kind: 'body'; readonly bodyId: string }

/** A wire's complete view-state (plan 22): the port binds, an optional branch
    hub, an optional ∃ tip body, an optional boundary frame-slot number, and the
    derived leg list (each leg carries only a memo cache — no shape state).

    A BOUNDARY wire (slot !== null) merges its hub and its frame exit: its ports
    meet at ONE junction body (`hub.kind === 'body'`, id `e:<wid>`) that is
    itself softly attracted to the fixed frame slot (relax.ts). The legs arrive
    at it with per-leg arrival angles + finite spread energy, exactly like an
    interior hub — so the boundary carries the tributary look — and the drawn
    frame connector runs that hub to the slot along the slot normal. There is no
    separate exit point and no stiff hub→exit leg (that pair was measured to
    destabilize). Because the exit hub rides ON the frame, it is excluded from
    the region enclosing circles (it is a boundary terminal, not content). */
export type WireView = {
  readonly binds: WireBind[]
  hub: WireHub | null
  readonly tipBodyId: string | null
  readonly slot: number | null
  readonly legs: WireLeg[]
  /** The hub's TRUNK AXIS (radians): the relaxed orientation along which the two
      most-opposite legs flow through as one continuous trunk while side legs
      merge tangentially (the tributary look, USER LAW). A DOF with inertia
      (gated descent + travel cap, so it never flips frame-to-frame), driven by
      the nematic alignment of the leg chord directions (relax.ts). Meaningful
      only for an interior hub (hub !== null && slot === null); 0 otherwise. */
  phi: number
}

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
  /** PLAN 22: each >= 1-endpoint wire is a massless-elastica view (binds +
      optional hub/tip + derived legs) — see elastica.ts + relax.ts for the
      energy model. Bare (0-endpoint) wires are a homed body only, no entry. */
  readonly wires: Map<WireId, WireView>
  readonly boundary: readonly WireId[]
  regions: Map<RegionId, RegionCircle>
  /** relaxation tick counter (drives overlap-projection cadence, determinism). */
  tick: number
  /** resume index into a time-sliced descent sweep (the app's anytime frame
      budget): the next DOF the budgeted stepper processes. 0 between sweeps and
      for the un-sliced full `settleStep`. */
  descentCursor: number
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

/** The nematic director of a set of directions: the axis (mod π) best aligned
    with them, `½·atan2(Σ sin2θ, Σ cos2θ)`. Degenerate (returns 0) only for a
    perfectly isotropic set, where every axis is equally good. Used to seed and
    anchor a hub's trunk axis to its leg chord directions. */
export function nematicDir(dirs: readonly number[]): number {
  let sc = 0, ss = 0
  for (const a of dirs) { sc += Math.cos(2 * a); ss += Math.sin(2 * a) }
  return 0.5 * Math.atan2(ss, sc)
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
      // seed a DISTINCT orientation per node (the same golden angle as the
      // position spiral): absolute orientation is a quotiented zero mode, but
      // starting every node at theta = 0 is a measure-zero degenerate config —
      // a port pointing exactly away from its fixed boundary slot then sits at
      // the energy's unstable maximum with a symmetric (zero) rotation
      // gradient and cannot roll off. A generic seed breaks the symmetry.
      pos: { x: Math.cos(ang) * rad, y: Math.sin(ang) * rad }, theta: (i + 1) * 2.399963,
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
        pos: { x: Math.cos(ang) * rad, y: Math.sin(ang) * rad }, theta: 0,
      })
      membersOf.get(rid)!.push(aid)
      i++
    }
  }

  const wires = new Map<WireId, WireView>()
  const bset = new Set(boundary)
  const slotOf = new Map(boundary.map((w, k) => [w, k] as const))
  // The line's OUTERMOST POINT is where its individual is quantified, and it
  // must be a body homed at the wire's SCOPE (USER LAW: dangling ends are
  // their own nodes — the ∃ is manipulable independently of what it attaches
  // to). A dangling wire's free tip IS that body; the ∀ via-body shape (scope
  // above the dca) grows a scope-homed branch body so the line never contorts
  // through its scope. Boundary wires get a frame-slot terminal instead.
  const mkWireBody = (id: string, region: RegionId, near: Vec2 | null): Body => {
    // seed NEAR the wire's own anchors, not on the global spiral: after a
    // rewrite, spiral-seeded ends left wires stretched wildly across the sheet
    const seed = near !== null
      ? { x: near.x + 4 + (i % 3), y: near.y - 3 - (i % 2) }
      : { x: (i++) * 3, y: -(i * 2) }
    i++
    const b: Body = {
      id, kind: 'junction', node: null, geometry: null,
      localAnchor: new Map(), discR: 4.5, region,
      pos: seed, theta: 0,
    }
    bodies.set(id, b)
    membersOf.get(region)!.push(id)
    return b
  }
  const mkLeg = (a: WireLegEnd, b: WireLegEnd, angle: number): WireLeg =>
    ({ a, b, hubAngle: angle, cache: mkLegCache() })
  const seedAngle = (p: Vec2, h: Vec2): number => Math.atan2(h.y - p.y, h.x - p.x)

  for (const [wid, w] of Object.entries(d.wires)) {
    const binds: WireBind[] = w.endpoints.map((ep) => ({ body: ep.node, key: pkey(ep.port) }))
    const isBoundary = bset.has(wid)
    if (binds.length === 0) {
      // a bare ∃ — the wire asserts only that an individual exists: one
      // scope-homed body, no legs (its dot is the whole rendering)
      mkWireBody(`j:${wid}`, w.scope, null)
      continue
    }
    const anchorPos = binds.map((bd) => worldBindAnchor(bodies.get(bd.body)!, bd.key))
    const centroid = (): Vec2 => ({
      x: anchorPos.reduce((s, p) => s + p.x, 0) / anchorPos.length,
      y: anchorPos.reduce((s, p) => s + p.y, 0) / anchorPos.length,
    })
    const dca = w.endpoints
      .map((ep) => d.nodes[ep.node]!.region)
      .reduce((a, b) => deepestCommonAncestor(d, a, b))

    let hub: WireHub | null = null
    let tipBodyId: string | null = null
    let slot: number | null = null
    const legs: WireLeg[] = []
    if (isBoundary) {
      // A boundary wire exits the sheet to a fixed frame slot. Its ports meet at
      // ONE junction body (`e:<wid>`) that is softly slot-attracted (relax.ts):
      // the hub and the exit are the SAME body, so there is no stiff hub→exit
      // pair (measured to destabilize). Each port reaches it with a hub leg
      // carrying its own arrival angle + finite spread energy (the tributary
      // look, as at an interior hub); the drawn frame connector runs the hub to
      // the slot. The exit hub, not the node, floats to the frame, so the layout
      // stays compact (a rigid slot pulling the node to the moving frame is a
      // measured runaway), and it is kept OUT of the region circles (it rides on
      // the frame, which the content defines) so the frame never chases it.
      slot = slotOf.get(wid)!
      const b = mkWireBody(`e:${wid}`, w.scope, centroid())
      hub = { kind: 'body', bodyId: b.id }
      for (let k = 0; k < binds.length; k++) legs.push(mkLeg({ kind: 'bind', i: k }, { kind: 'hub' }, seedAngle(anchorPos[k]!, b.pos)))
    } else if (binds.length === 1) {
      // dangling ∃: a free-end leg reaching a scope-homed tip body
      const b = mkWireBody(`j:${wid}`, w.scope, anchorPos[0]!)
      tipBodyId = b.id
      legs.push(mkLeg({ kind: 'bind', i: 0 }, { kind: 'tip' }, 0))
    } else if (w.scope !== dca) {
      // the ∀ via-body: the scope-homed body IS the branch hub
      const b = mkWireBody(`x:${wid}`, w.scope, centroid())
      hub = { kind: 'body', bodyId: b.id }
      for (let k = 0; k < binds.length; k++) legs.push(mkLeg({ kind: 'bind', i: k }, { kind: 'hub' }, seedAngle(anchorPos[k]!, b.pos)))
    } else if (binds.length === 2) {
      // a direct port-to-port leg (same scope, no branch)
      legs.push(mkLeg({ kind: 'bind', i: 0 }, { kind: 'bind', i: 1 }, 0))
    } else {
      // a pure k-ary junction: a wire-owned hub point
      const h = centroid()
      hub = { kind: 'point', pos: h }
      for (let k = 0; k < binds.length; k++) legs.push(mkLeg({ kind: 'bind', i: k }, { kind: 'hub' }, seedAngle(anchorPos[k]!, h)))
    }
    // seed the trunk axis at the nematic director of the interior hub's chord
    // directions (so the trunk lands aligned instead of swinging in from 0)
    let phi = 0
    if (hub !== null && !isBoundary) {
      const hp = hub.kind === 'point' ? hub.pos : bodies.get(hub.bodyId)!.pos
      phi = nematicDir(anchorPos.map((p) => Math.atan2(p.y - hp.y, p.x - hp.x)))
    }
    wires.set(wid, { binds, hub, tipBodyId, slot, legs, phi })
  }

  return { d, bodies, childrenOf, membersOf, wires, boundary, regions: new Map(), tick: 0, descentCursor: 0 }
}

/**
 * Transplant the layout state of every body shared between two engines. When a
 * new engine is built for the next diagram in a replay, bodies whose id survives
 * (nodes keyed by NodeId, junctions by `j:<wireId>`) keep their pos/theta so
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
    nb.theta = pb.theta
  }
  // wires glide too: a surviving wire with the same bind signature keeps its
  // hub/exit position and per-leg arrival angles instead of re-seeding.
  // The legs' geometry is memoryless (recomputed), so only the DOF carry.
  const sig = (v: WireView): string =>
    [...v.binds.map((b) => `${b.body}:${b.key}`), v.hub === null ? '-' : v.hub.kind, v.tipBodyId ?? '-', v.slot ?? '-'].join('|')
  for (const [wid, nv] of next.wires) {
    const pv = prev.wires.get(wid)
    if (pv === undefined || sig(pv) !== sig(nv)) continue
    if (nv.hub !== null && nv.hub.kind === 'point' && pv.hub !== null && pv.hub.kind === 'point') {
      nv.hub.pos = pv.hub.pos
    }
    for (let k = 0; k < nv.legs.length && k < pv.legs.length; k++) {
      nv.legs[k]!.hubAngle = pv.legs[k]!.hubAngle
    }
    nv.phi = pv.phi
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

/** Where a WIRE attaches to a body: the point on the DRAWN node outline in the
    port's direction, so the wire touches the surface the user sees (USER LAW:
    wire endpoints locked to the node rim, perpendicular exit BY CONSTRUCTION).
    `discR` is the padded CLEARANCE disc, not the drawing — attaching there floats
    the wire a pad-width off the rendered rim (USER report: floating attachments).

    A ref discards its anatomy for a readable labelled disc drawn at DISC_R, so
    its wire meets that drawn rim at DISC_R along the port direction. An atom or a
    term draws its real anatomy with a radial port stub whose TIP is the port
    anchor (bend.ts / atomGeometry), so the wire meets that drawn stub tip
    directly — the port anchor is already on the drawing (ascale folded in). */
export function worldBindAnchor(b: Body, key: string): Vec2 {
  const a = b.localAnchor.get(key)!
  const c = Math.cos(b.theta), s = Math.sin(b.theta)
  if (b.kind === 'ref') {
    const la = Math.hypot(a.x, a.y)
    const ux = la < 1e-9 ? 1 : a.x / la, uy = la < 1e-9 ? 0 : a.y / la
    return { x: b.pos.x + (ux * c - uy * s) * DISC_R, y: b.pos.y + (ux * s + uy * c) * DISC_R }
  }
  return { x: b.pos.x + a.x * c - a.y * s, y: b.pos.y + a.x * s + a.y * c }
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

/** A leg's resolved boundary data + its minimum-energy solution. The endpoints
    are DERIVED from the live bodies/hub/slot every call (never stored); `sol`
    is the memoized θ-quadratic. `ownA`/`ownB` name the discs a bind end sits
    on (exempt near their rim in the clearance integral). */
export type LegShape = {
  readonly sol: Sol
  readonly p0: Vec2; readonly th0: number
  readonly p1: Vec2; readonly th1: number
  readonly freeEnd: boolean
  readonly ownA: string | null
  readonly ownB: string | null
}
/** Width of the escape ramp ABOVE π (radians). */
export const STRESS_BAND = Math.PI / 3

/** Resolve + solve one leg against the live state. Terminal `a` is a port bind
    leaving along its outward normal (rim-locked, perpendicular exit BY
    CONSTRUCTION — the solve fixes θ(0)=normal); terminal `b` arrives with
    travel direction th1: the hub arrival angle, INTO a far port (normal+π), or
    a free end at an ∃ tip (no arrival tangent).

    `warm` = a base solution to WARM-solve against (gradient probes): rather
    than the full memoryless grid scan, close the endpoints at the base's total
    turning (a single Newton). The base is the tau-minimizer, so by the
    envelope theorem the fixed-tau energy has the same first-order DOF gradient
    — correct for central differences, ~15× cheaper. Otherwise the full
    memoryless solve runs, memoized on `cache`. */
export function resolveLeg(e: Engine, w: WireView, leg: WireLeg, cache: LegCache = leg.cache, warm: Sol | null = null): LegShape {
  const hubPos = (): Vec2 => {
    const h = w.hub!
    return h.kind === 'point' ? h.pos : e.bodies.get(h.bodyId)!.pos
  }
  // terminal A is always a port bind (leaves along its outward normal — the
  // rim-locked perpendicular exit BY CONSTRUCTION)
  const bd0 = w.binds[leg.a.kind === 'bind' ? leg.a.i : 0]!
  const b0 = e.bodies.get(bd0.body)!
  const p0 = worldBindAnchor(b0, bd0.key)
  const la0 = b0.localAnchor.get(bd0.key)!
  const th0 = Math.atan2(la0.y, la0.x) + b0.theta
  const ownA: string | null = bd0.body
  let p1: Vec2, th1: number, freeEnd = false
  let ownB: string | null = null
  switch (leg.b.kind) {
    // a BOUNDARY exit hub leg is a FREE end (zero moment): the global-rotation
    // DOF (relax.ts) spins the content so the port faces its slot, so the leg
    // needs no arrival well to reach the slot-attracted hub, and a free end never
    // charges a blind-cone well that would fight the alignment.
    case 'hub': { p1 = hubPos(); th1 = leg.hubAngle; if (w.slot !== null) freeEnd = true; break }
    case 'tip': { p1 = e.bodies.get(w.tipBodyId!)!.pos; th1 = 0; freeEnd = true; break }
    default: {
      const bd = w.binds[leg.b.i]!
      const b = e.bodies.get(bd.body)!
      p1 = worldBindAnchor(b, bd.key)
      const la = b.localAnchor.get(bd.key)!
      th1 = Math.atan2(la.y, la.x) + b.theta + Math.PI
      ownB = bd.body
    }
  }
  let sol: Sol
  if (warm !== null) {
    const r = closeAt(p0, th0, p1, warm.dTurn, warm.c1, warm.L)
    const c1 = r.ok ? r.c1 : warm.c1
    const L = r.ok ? r.L : warm.L
    sol = { c1, c2: warm.dTurn - c1, L, dTurn: warm.dTurn, well: freeEnd ? 0 : WELL_S * (1 - Math.cos(th0 + warm.dTurn - th1)) }
  } else {
    sol = solveLeg(cache, p0, th0, p1, th1, freeEnd)
  }
  // NO length cap here: a blind-cone leg (target > ~138° behind the port — no
  // range ≤ π solution) must keep its true, steeply-increasing fallback length
  // so it stays energetically REPULSIVE — that is the gradient a movable hub/tip
  // needs to migrate OUT of the cone and the node needs to rotate to face its
  // target. The tau → 2π singularity is regularized inside solveLeg (finite but
  // steep), so L is bounded without flattening the gradient.
  return { sol, p0, th0, p1, th1, freeEnd, ownA, ownB }
}

/** Trace a resolved leg into world-space sample points (n segments). */
export function traceLeg(s: LegShape, out: Vec2[], n: number = QN): void {
  trace(s.p0, s.th0, s.sol.c1, s.sol.c2, s.sol.L, out, n)
}
