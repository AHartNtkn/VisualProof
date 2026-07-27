import type { Diagram, DiagramNode, NodeId, Port, RegionId, WireId } from '../kernel/diagram/diagram'
import { requiredPorts, portKey } from '../kernel/diagram/diagram'
import { deepestCommonAncestor } from '../kernel/diagram/regions'
import type { Vec2 } from './vec'
import { add } from './vec'
import type { NodeGeometry } from './bend'
import { atomGeometry, identityGeometry, refGeometry } from './bend'
import type { Disc } from './route/freespace'
import type { CurveBC } from './route/curve'
import type { WireNet } from './route/network'

/**
 * The converged render engine (round-8 lab spec). A Diagram-plus-boundary is
 * lifted into a set of relaxation BODIES — one per node, plus one wire-owned END
 * body for every ∃/∀ quantifier point (the loose ∃ tip, the ∀ via, a bare ∃) —
 * each carrying its local anatomy geometry and an enclosing disc radius.
 * Positions/rotations are relaxed by `relax.ts`; geometry is emitted by
 * `wires.ts`/`paint.ts`. Nothing here is semantic and nothing is serialized.
 *
 * ROUTED-NETWORK WIRES (USER ruling 2026-07-24): a wire is one explicit graph
 * over its terminals (port ESCAPE points, boundary slots, free ∃/∀ endpoint
 * bodies) and junction vertices of ARBITRARY degree ≥ 3. Edges are incidences
 * only — no tangents, no curvature basins, no per-edge physical identity.
 * Routing is deterministic shortest paths through free space with every node
 * disc inflated as a HARD obstacle (src/view/route/). A port terminal is a
 * fixed rim point plus an outward clamp normal; the drawn stroke is the
 * Hobby cubic chain over the routed corridor (route/curve.ts); no curve
 * state exists anywhere. ∃/∀ quantifier points stay first-class END
 * bodies serving as terminals.
 */

/** Standard named-disc radius (world units) — one size for every named disc. */
export const DISC_R = 5.5
/** Sheet frame margin beyond the outermost region (world units). */
export const FRAME_MARGIN = 6
/** Corner radius of the sheet frame, world units — shared by the drawn
    rounded rectangle and the boundary-exit geometry so exits ride the
    visible frame line exactly. */
export const FRAME_CORNER_W = 8

export type BodyKind = 'ref' | 'atom' | 'identity' | 'end' | 'anchor'

export type Body = {
  readonly id: string
  readonly kind: BodyKind
  readonly node: DiagramNode | null
  readonly geometry: NodeGeometry | null
  /** Port key (pkey) -> anatomy-local anchor, ascale already folded in. */
  readonly localAnchor: Map<string, Vec2>
  /** NATURAL clearance-disc radius (scale 1). The world radius is
      `discR * Engine.scale`: content scale belongs to the engine, never to an
      individual body, so every body always contains only natural geometry. */
  readonly discR: number
  readonly region: RegionId
  pos: Vec2
  theta: number
}

/** key null = the body's centre (end bodies have no ports). */
export type LegEnd = { readonly body: string; readonly key: string | null }
export type Leg = { readonly wid: WireId; readonly from: LegEnd; readonly to: LegEnd }

// ---- the routed-network wire view-state (USER ruling 2026-07-24) -----------

/** A wire endpoint bound to a node port (the disc-edge rim anchor + the port
    normal are DERIVED from the body each evaluation — never stored). */
export type WireBind = { readonly body: string; readonly key: string }

/** A wire's complete view-state: node-port binds, zero or more ordered
    boundary incidences, an optional wire-owned END body, and the routed
    NETWORK `net` — junction positions plus graph edges over the vertex
    indexing [binds..., slots..., end?][then junctions]. The router owns
    `net`; nothing else writes it. */
export type WireView = {
  readonly binds: WireBind[]
  /** The wire's single wire-owned END body id (the ∃ tip, the ∀ via, or a bare
      ∃ dot), or null. A terminal of the network. */
  readonly endBodyId: string | null
  readonly slots: readonly number[]
  readonly net: WireNet
}

/** A region's drawn circle. `support` lists the direct items (member body or
    child region) ON the rim — the only content the circle's geometry depends
    on, and therefore where region-level forces land. */
export type RegionCircle = { center: Vec2; radius: number; support: readonly { mid?: string; sub?: RegionId }[] }

export type Engine = {
  readonly d: Diagram
  readonly bodies: Map<string, Body>
  readonly childrenOf: Map<RegionId, RegionId[]>
  /** node / wire-owned END-body / anchor ids per region. */
  readonly membersOf: Map<RegionId, string[]>
  /** Every boundary wire and each >= 1-endpoint internal wire is a routed
      NETWORK view (binds + optional wire-owned END body [∃ tip / ∀ via] +
      the wire's graph) — see src/view/route/. A bare boundary wire is a
      bodyless, zero-edge view at its fixed slot; only a bare internal wire
      is a homed body with no entry. */
  readonly wires: Map<WireId, WireView>
  readonly boundary: readonly WireId[]
  regions: Map<RegionId, RegionCircle>
  /** The fixed near-square proof frame (plan 24): the statement boundary box, an
      ABSOLUTE stored state — established ONCE from the content extent at first spawn
      (after the leading construction projection makes the seed legal) and CONSTANT
      for the diagram's ENTIRE LIFETIME (USER RULING 2026-07-06: the border NEVER
      resizes — a rewrite carries the SAME frame via carryOver, content reflows
      inside). It never grows/shrinks from motion OR from a rewrite: settling,
      dragging, free relaxation, and proof steps read it but never write it. Null
      until the first establishment. `half` is the half-extent of both axes
      (near-square: sized to the larger content half-extent + margin), so a wide
      proof gets a bigger square, never a letterbox. */
  frame: StoredFrame | null
  /** Per-step CONTENT-FILL scale (plan 24): the uniform length multiplier that
      sizes this step's content to fill the FIXED proof-wide border (the border
      never resizes — USER LAW; the CONTENT does, per rewrite). This is the sole
      content-scale authority: relax reads it for packing/clearance lengths and
      engine + paint read it for world geometry. Bodies retain natural geometry.
      1 = natural size. */
  scale: number
  /** Boundary SLOT-SHIFT (plan 24 legibility, USER 2026-07-07): a single cyclic
      rotation of the wire→slot assignment (boundary wire i attaches to slot
      (i + slotShift) mod n) chosen ONCE to minimize the total port→slot chord — the
      even-spaced slots start at an arbitrary top-centre phase, so without this a
      port near one edge can be assigned a slot on the far edge and its wire sweeps
      the whole frame (then hugs the inside border). Only CYCLIC shifts are used
      (they preserve the canonical cyclic order / no-slipping law); the prominent
      origin marker stays with logical port 0 and follows it to the assigned shifted
      slot. Computed
      proof-wide (min total chord over all steps' seeds), carried across the proof,
      never changed mid-proof. 0 = unshifted. */
  slotShift: number
  /** relaxation tick counter (drives overlap-projection cadence, determinism). */
  tick: number
}

/** Optional source→target graph identity for carrying view state across renamed
    but canonically corresponding replay representations. */
export type LayoutIdentity = {
  readonly regions: ReadonlyMap<RegionId, RegionId>
  readonly nodes: ReadonlyMap<NodeId, NodeId>
  readonly wires: ReadonlyMap<WireId, WireId>
}

/** The fixed proof frame: centre + half-extent of a near-square rounded box. */
export type StoredFrame = { readonly center: Vec2; readonly half: number }

/** Local anatomy scale per node kind. */
export function ascaleOf(kind: BodyKind): number {
  return kind === 'atom' ? 2 : kind === 'identity' ? 1.4 : 1
}

export function pkey(p: Port): string {
  return portKey(p)
}

/** Exact local geometry for one atom, ref, or identity node. */
export function nodeGeometry(d: Diagram, id: NodeId): NodeGeometry {
  const n = d.nodes[id]
  if (n === undefined) throw new Error(`unknown node '${id}'`)
  switch (n.kind) {
    case 'atom':
      return atomGeometry(n.sig.args.length)
    case 'ref':
      return refGeometry(n.sig.args.length)
    case 'identity':
      return identityGeometry(n.arity)
  }
}

/** World-space anchor of (geometry, centre, port). */
export function anchorOf(geometry: NodeGeometry, center: Vec2, port: Port): Vec2 {
  if (port.kind === 'head') {
    if (geometry.headAnchor === null) throw new Error('geometry has no head anchor for a head port')
    return add(center, geometry.headAnchor)
  }
  const key = portKey(port)
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
    for (const port of requiredPorts(n)) {
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
  // Construct the engine before deriving any wire geometry. Even the natural
  // scale-1 seed path uses the same engine-aware geometry helpers as live
  // rendering and physics, so there is no second raw-scale geometry path.
  const engine: Engine = {
    d, bodies, childrenOf, membersOf, wires, boundary,
    regions: new Map(), frame: null, scale: 1, slotShift: 0, tick: 0,
  }
  const slotsOf = new Map<WireId, number[]>()
  boundary.forEach((wid, position) => {
    const positions = slotsOf.get(wid)
    if (positions === undefined) slotsOf.set(wid, [position])
    else positions.push(position)
  })
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
      id, kind: 'end', node: null, geometry: null,
      localAnchor: new Map(), discR: 4.5, region,
      pos: seed, theta: 0,
    }
    bodies.set(id, b)
    membersOf.get(region)!.push(id)
    return b
  }
  for (const [wid, w] of Object.entries(d.wires)) {
    const binds: WireBind[] = w.endpoints.map((ep) => ({ body: ep.node, key: pkey(ep.port) }))
    const slots = slotsOf.get(wid) ?? []
    const isBoundary = slots.length > 0
    if (!isBoundary && binds.length === 0) {
      // A bare INTERNAL ∃ — the wire asserts only that an individual exists:
      // one scope-homed body, no edges (its dot is the whole rendering).
      mkWireBody(`j:${wid}`, w.scope, null)
      continue
    }
    const anchorPos = binds.map((bd) => worldBindAnchor(engine, bodies.get(bd.body)!, bd.key))
    const centroid = (): Vec2 => binds.length === 0
      ? { x: 0, y: 0 }
      : {
          x: anchorPos.reduce((s, p) => s + p.x, 0) / anchorPos.length,
          y: anchorPos.reduce((s, p) => s + p.y, 0) / anchorPos.length,
        }

    let endBodyId: string | null = null
    if (isBoundary) {
      // port binds + boundary incidences are the terminals; the line exits to the frame.
    } else if (binds.length === 1) {
      endBodyId = mkWireBody(`j:${wid}`, w.scope, anchorPos[0]!).id
    } else if (w.scope !== w.endpoints
      .map((ep) => d.nodes[ep.node]!.region)
      .reduce((a, b) => deepestCommonAncestor(d, a, b))) {
      // the ∀ via-body: a scope-homed END body, an ordinary terminal of the network.
      endBodyId = mkWireBody(`x:${wid}`, w.scope, centroid()).id
    }
    // Initial topology: <2 terminals → no edges; 2 → one direct edge; ≥3 → a
    // STAR on one junction at the terminal centroid. The split rule (the
    // tangent-cone derivative of routed length) refines the star into the
    // proper Steiner topology on the first advanceNetwork frames — no
    // topology seeder exists.
    const nT = binds.length + slots.length + (endBodyId !== null ? 1 : 0)
    const net: WireNet = { junctions: [], edges: [] }
    if (nT === 2) net.edges = [[0, 1]]
    else if (nT >= 3) {
      const c = centroid()
      net.junctions = [{ x: c.x, y: c.y }]
      net.edges = Array.from({ length: nT }, (_, t) => [t, nT] as const)
    }
    wires.set(wid, { binds, endBodyId, slots, net })
  }

  return engine
}

/**
 * Transplant the layout state of every corresponding body between two engines.
 * Raw IDs are the default correspondence; replay may supply canonical view
 * identity for an exact endpoint whose graph IDs differ from the computed proof
 * form. Nodes, region anchors, and wire-owned `j:`/`x:` END bodies keep their
 * pos/theta so the layout glides rather than re-seeding from the spiral.
 * Bodies present only in `next` keep their deterministic mkEngine seeds. Vec2 is
 * treated as an immutable value here, matching relax.ts's replace-not-mutate
 * discipline, so copying the reference cannot alias `prev` into `next`'s motion.
 */
export function carryOver(
  prev: Engine,
  next: Engine,
  identity?: LayoutIdentity,
): void {
  // The border NEVER resizes for the diagram's lifetime (USER RULING 2026-07-06):
  // a rewrite keeps the SAME frame — content reflows inside the unchanged box, the
  // box is not recomputed. Carrying prev.frame makes `establishFrame` a no-op on the
  // rebuilt engine (it only establishes when frame === null), so the drawn border is
  // byte-identical across every step of a proof.
  next.frame = prev.frame
  // Carry prev's layout NORMALIZED to natural scale (plan 24): prev was displayed at
  // its own content-fill scale, so un-scale every carried position about the frame
  // centre back to scale 1. The rebuilt engine is then a clean natural (scale-1)
  // layout — new bodies are already seeded natural — and `applyContentScale`
  // (seedProject) re-solves THIS step's fill scale and scales the whole thing up
  // uniformly. The relative layout GLIDES (positions are prev's, just re-sized); the
  // size change is the sanctioned discrete-event recalc at the rewrite.
  next.scale = 1
  // the boundary slot-shift is a proof-wide constant (chosen once at enterReplay) —
  // carry it so slots never reorder mid-proof.
  next.slotShift = prev.slotShift
  const c = prev.frame === null ? { x: 0, y: 0 } : prev.frame.center
  const denorm = (p: Vec2, sc: number): Vec2 => ({ x: c.x + (p.x - c.x) / sc, y: c.y + (p.y - c.y) / sc })
  const mappedBodyId = (id: string): string | undefined => {
    if (identity === undefined) return id
    if (prev.d.nodes[id] !== undefined) return identity.nodes.get(id)
    for (const prefix of ['j:', 'x:'] as const) {
      if (id.startsWith(prefix)) {
        const wire = identity.wires.get(id.slice(prefix.length))
        return wire === undefined ? undefined : `${prefix}${wire}`
      }
    }
    if (id.startsWith('anchor:')) {
      const region = identity.regions.get(id.slice('anchor:'.length))
      return region === undefined ? undefined : `anchor:${region}`
    }
    return undefined
  }
  for (const [id, pb] of prev.bodies) {
    const targetId = mappedBodyId(id)
    if (targetId === undefined) continue
    const nb = next.bodies.get(targetId)
    if (nb === undefined) continue
    nb.pos = denorm(pb.pos, prev.scale)
    nb.theta = pb.theta
  }
  // A surviving wire carries its NETWORK (junction positions + graph edges),
  // keyed on wire IDENTITY (the terminal set), exactly as node positions are
  // carried. The router re-solves from the carried state; nothing re-derives.
  const sig = (v: WireView): string =>
    [...v.binds.map((b) => `${b.body}:${b.key}`), v.endBodyId === null ? '-' : 'end', `slots:${v.slots.join(',')}`].join('|')
  const terminalImage = (
    from: WireView,
    to: WireView,
  ): readonly number[] | null => {
    const fromHasEnd = from.endBodyId !== null
    const toHasEnd = to.endBodyId !== null
    if (
      fromHasEnd !== toHasEnd
      || from.slots.length !== to.slots.length
      || from.slots.some((slot, index) => slot !== to.slots[index])
    ) {
      return null
    }
    const image: number[] = []
    const used = new Set<number>()
    for (const bind of from.binds) {
      const body = identity!.nodes.get(bind.body)
      if (body === undefined) return null
      const target = to.binds.findIndex((candidate, index) =>
        !used.has(index)
        && candidate.body === body
        && candidate.key === bind.key)
      if (target < 0) return null
      used.add(target)
      image.push(target)
    }
    if (used.size !== to.binds.length) return null
    for (let index = 0; index < from.slots.length; index++) {
      image.push(to.binds.length + index)
    }
    if (fromHasEnd) {
      image.push(to.binds.length + to.slots.length)
    }
    return image
  }
  for (const [wid, pv] of prev.wires) {
    const targetWire = identity === undefined ? wid : identity.wires.get(wid)
    if (targetWire === undefined) continue
    const nv = next.wires.get(targetWire)
    if (nv === undefined) continue
    if (identity === undefined) {
      if (sig(pv) !== sig(nv)) continue
      nv.net.junctions = pv.net.junctions.map((p) => denorm(p, prev.scale))
      nv.net.edges = pv.net.edges.map(([u, v]) => [u, v])
      continue
    }
    const terminalMap = terminalImage(pv, nv)
    if (terminalMap === null) continue
    const fromTerminalCount = terminalMap.length
    const toTerminalCount = nv.binds.length + nv.slots.length
      + (nv.endBodyId === null ? 0 : 1)
    const vertexImage = (vertex: number): number =>
      vertex < fromTerminalCount
        ? terminalMap[vertex]!
        : toTerminalCount + vertex - fromTerminalCount
    nv.net.junctions = pv.net.junctions.map((p) => denorm(p, prev.scale))
    nv.net.edges = pv.net.edges.map(([u, v]) => [
      vertexImage(u),
      vertexImage(v),
    ])
  }
}

/** Map an anatomy-local point (before ascale) into world space through the
    engine's authoritative content scale and the body's pose. */
export function localToWorld(e: Engine, b: Body, lp: Vec2): Vec2 {
  const ascale = ascaleOf(b.kind) * e.scale
  const c = Math.cos(b.theta), s = Math.sin(b.theta)
  const x = lp.x * ascale, y = lp.y * ascale
  return { x: b.pos.x + x * c - y * s, y: b.pos.y + x * s + y * c }
}

/** World anchor of (body, port key); key null returns the body centre. */
export function worldAnchor(e: Engine, b: Body, key: string | null): Vec2 {
  if (key === null) return b.pos
  const a0 = b.localAnchor.get(key)!
  const a = { x: a0.x * e.scale, y: a0.y * e.scale }
  const c = Math.cos(b.theta), s = Math.sin(b.theta)
  return { x: b.pos.x + a.x * c - a.y * s, y: b.pos.y + a.x * s + a.y * c }
}

/** Where a WIRE attaches to a body: the point on the DRAWN node outline in the
    port's direction, so the wire touches the surface the user sees (USER LAW:
    wire endpoints locked to the node rim, perpendicular exit BY CONSTRUCTION).
    `discR` is the padded CLEARANCE disc, not the drawing — attaching there floats
    the wire a pad-width off the rendered rim (USER report: floating attachments).

    A ref uses a readable labelled disc drawn at DISC_R, so its wire meets that
    drawn rim at DISC_R along the port direction. Atom and identity ports sit
    on their rail rims, so their anchors already lie on the drawing. */
export function worldBindAnchor(e: Engine, b: Body, key: string): Vec2 {
  const a0 = b.localAnchor.get(key)!
  const c = Math.cos(b.theta), s = Math.sin(b.theta)
  if (b.kind === 'ref') {
    const la = Math.hypot(a0.x, a0.y)
    const ux = la < 1e-9 ? 1 : a0.x / la, uy = la < 1e-9 ? 0 : a0.y / la
    const R = DISC_R * e.scale
    return { x: b.pos.x + (ux * c - uy * s) * R, y: b.pos.y + (ux * s + uy * c) * R }
  }
  const a = { x: a0.x * e.scale, y: a0.y * e.scale }
  return { x: b.pos.x + a.x * c - a.y * s, y: b.pos.y + a.x * s + a.y * c }
}

/** The outward normal at (body, port key), in world radians. End bodies have no
    ports, so their "normal" is the direction toward the far endpoint. */
export function portNormal(b: Body, key: string | null, toward: Vec2): number {
  if (key === null) return Math.atan2(toward.y - b.pos.y, toward.x - b.pos.x)
  const a = b.localAnchor.get(key)!
  return Math.atan2(a.y, a.x) + b.theta
}

export type FrameBounds = { minX: number; maxX: number; minY: number; maxY: number; frameR: number; center: Vec2 }

/** The fixed near-square proof frame box, read from the stored frame state (plan
    24). Null before the frame is established (the leading construction projection
    at each spawn/rewrite establishes it — see relax.ts `establishFrame`). It is a
    CONSTANT between rewrites: never derived from per-tick region geometry, so the
    box does not breathe as content settles. `frameR` is the square half-extent. */
export function frameBounds(e: Engine): FrameBounds | null {
  const f = e.frame
  if (f === null) return null
  return {
    minX: f.center.x - f.half, maxX: f.center.x + f.half,
    minY: f.center.y - f.half, maxY: f.center.y + f.half,
    frameR: f.half, center: f.center,
  }
}

/** A boundary slot: a fixed perimeter point plus the outward frame normal there. */
export type FrameSlot = { readonly point: Vec2; readonly normal: number }

/**
 * The n boundary slots: points spaced evenly BY ARC LENGTH around the frame's
 * rounded-rectangle perimeter, physical slot 0 at the top-edge midpoint
 * and proceeding CLOCKWISE (canvas y-down). `normal` is the outward frame normal
 * — axis-aligned on a straight edge, radial from the corner centre on a corner
 * (the same rounded rect paint draws, so a slot rides the visible frame line).
 * Logical boundary wire i is assigned through `resolvedFrameSlot`, which applies
 * the proof-wide cyclic shift while preserving order; wires structurally cannot
 * pass one another.
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

/** The live frame slot assigned to one logical boundary position. This is the
    single geometry authority used by leg solving, painting, and hit testing. */
export function resolvedFrameSlot(e: Engine, boundaryPosition: number): FrameSlot | null {
  if (boundaryPosition < 0 || boundaryPosition >= e.boundary.length) return null
  const fb = frameBounds(e)
  if (fb === null) return null
  return frameSlots(fb, e.boundary.length)[(boundaryPosition + e.slotShift) % e.boundary.length] ?? null
}

/** Wire routing clearance beyond a node's drawn disc (natural units; the
    world clearance scales with the content fill). Routes treat every node
    disc inflated by this as a HARD obstacle. */
export const ROUTE_CLEAR = 1.5

/** Routing bounds: the fixed frame's inner box (nothing routed outside). */
export function routeBounds(e: Engine): { minX: number; maxX: number; minY: number; maxY: number } | null {
  const fb = frameBounds(e)
  if (fb === null) return null
  return { minX: fb.minX, maxX: fb.maxX, minY: fb.minY, maxY: fb.maxY }
}

/** The inflated hard-obstacle discs for wire routing. */
export function routeObstacles(e: Engine): Disc[] {
  const out: Disc[] = []
  for (const b of e.bodies.values()) {
    if (b.kind !== 'ref' && b.kind !== 'atom' && b.kind !== 'identity') continue
    out.push({ c: b.pos, r: (b.discR + ROUTE_CLEAR) * e.scale })
  }
  return out
}

/** The fixed escape stub of a port bind: from the rim anchor outward along
    the port normal to just past the inflated obstacle disc. The optimized
    network begins at the escape point; the stub itself is fixed geometry
    (perpendicular exit BY CONSTRUCTION — the connected node is never a
    special case in the router). */
export function escapePoint(e: Engine, bd: WireBind): { anchor: Vec2; escape: Vec2 } {
  const b = e.bodies.get(bd.body)!
  const anchor = worldBindAnchor(e, b, bd.key)
  const la = b.localAnchor.get(bd.key)!
  const n = Math.atan2(la.y, la.x) + b.theta
  const nx = Math.cos(n), ny = Math.sin(n)
  const R = (b.discR + ROUTE_CLEAR) * e.scale + 1e-3
  // solve |anchor + n·t − c| = R for the smallest t ≥ 0 (anchor is inside R)
  const ax = anchor.x - b.pos.x, ay = anchor.y - b.pos.y
  const pn = ax * nx + ay * ny
  const disc = pn * pn - (ax * ax + ay * ay - R * R)
  const t = disc <= 0 ? R : -pn + Math.sqrt(disc)
  return { anchor, escape: { x: anchor.x + nx * Math.max(t, 0), y: anchor.y + ny * Math.max(t, 0) } }
}

/** A boundary slot's fixed INWARD stub: the drawn stroke meets the frame
    perpendicular by construction (the network attaches at the stub's inner
    end; the renderer appends the frame point). */
export function slotEscape(e: Engine, position: number): { point: Vec2; inner: Vec2 } | null {
  const s = resolvedFrameSlot(e, position)
  if (s === null) return null
  const t = 2 * ROUTE_CLEAR * e.scale
  return {
    point: s.point,
    inner: { x: s.point.x - Math.cos(s.normal) * t, y: s.point.y - Math.sin(s.normal) * t },
  }
}

/** Curve boundary condition per terminal, in network vertex order: the fixed
    anchor point and the unit direction the drawn curve LEAVES it (a port's
    outward normal; a frame slot's inward normal), or null for a free ∃/∀ end
    dot (natural end at the dot). The drawn curve of a terminal-incident edge
    is CLAMPED here — perpendicular port/frame meetings by energy. */
export function wireTerminalBCs(e: Engine, w: WireView): CurveBC[] {
  const out: CurveBC[] = w.binds.map((bd) => {
    const b = e.bodies.get(bd.body)!
    const la = b.localAnchor.get(bd.key)!
    const a = Math.atan2(la.y, la.x) + b.theta
    return {
      p: worldBindAnchor(e, b, bd.key),
      n: { x: Math.cos(a), y: Math.sin(a) },
    }
  })
  for (const position of w.slots) {
    const s = resolvedFrameSlot(e, position)
    out.push(s === null ? null : { p: s.point, n: { x: -Math.cos(s.normal), y: -Math.sin(s.normal) } })
  }
  if (w.endBodyId !== null) out.push(null)
  return out
}

/** The wire's terminal POINTS in network vertex order (binds, slots, end).
    Pure read of the live geometry; the router treats these as fixed. */
export function wireTerminalPoints(e: Engine, w: WireView): Vec2[] {
  const pts: Vec2[] = w.binds.map((bd) => escapePoint(e, bd).escape)
  for (const position of w.slots) {
    const s = slotEscape(e, position)
    if (s !== null) pts.push(s.inner)
    else {
      const c: Vec2 = pts.length === 0
        ? { x: 0, y: 0 }
        : { x: pts.reduce((a, p) => a + p.x, 0) / pts.length, y: pts.reduce((a, p) => a + p.y, 0) / pts.length }
      const angle = -Math.PI / 2 + (2 * Math.PI * position) / Math.max(1, e.boundary.length)
      pts.push({ x: c.x + 30 * Math.cos(angle), y: c.y + 30 * Math.sin(angle) })
    }
  }
  if (w.endBodyId !== null) pts.push(e.bodies.get(w.endBodyId)!.pos)
  return pts
}
