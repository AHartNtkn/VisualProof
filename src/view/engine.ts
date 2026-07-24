import type { Diagram, DiagramNode, NodeId, Port, RegionId, WireId } from '../kernel/diagram/diagram'
import { requiredPorts, portKey } from '../kernel/diagram/diagram'
import { deepestCommonAncestor } from '../kernel/diagram/regions'
import type { Vec2 } from './vec'
import { add } from './vec'
import { buildJunctionTree } from './soaptree'
import type { NodeGeometry } from './bend'
import { bendGrid, atomGeometry, refGeometry, bodyGeometry } from './bend'
import { trompGrid } from './tromp'
import type { LegCache, Sol } from './elastica'
import { mkLegCache, solveLeg, closeAt, trace, QN, WELL_S } from './elastica'

/**
 * The converged render engine (round-8 lab spec). A Diagram-plus-boundary is
 * lifted into a set of relaxation BODIES — one per node, plus one wire-owned END
 * body for every ∃/∀ quantifier point (the loose ∃ tip, the ∀ via, a bare ∃) —
 * each carrying its local anatomy geometry and an enclosing disc radius.
 * Positions/rotations are relaxed by `relax.ts`; geometry is emitted by
 * `wires.ts`/`paint.ts`. Nothing here is semantic and nothing is serialized.
 *
 * PLAN 22: wires are MASSLESS ELASTICA (see elastica.ts). A wire has no shape
 * state — each leg is the minimum-energy theta-quadratic interpolant of its
 * CURRENT boundary data, recomputed per evaluation and memoized on the exact
 * boundary tuple.
 *
 * A wire's junction state is exactly (T, b, τ): the tree TOPOLOGY T and its
 * per-half-edge tangents τ live together in `legs` (each leg is one tree edge,
 * its ends the tree vertices, its `angA/angB` the τ), the branch-vertex
 * POSITIONS b live in `branches`. There is NO 'junction' notion in the data:
 * where legs meet is downstream of which tree T is picked. The wire DOF are the
 * branch positions and the per-leg tangents; ∃/∀ quantifier points stay
 * first-class END bodies serving as free-end LEAF terminals of the tree. Loops
 * and kinks are UNREPRESENTABLE (tangent range <= pi).
 */

/** Standard named-disc radius (world units) — one size for every named disc. */
export const DISC_R = 5.5
/** Sheet frame margin beyond the outermost region (world units). */
export const FRAME_MARGIN = 6
/** Corner radius of the sheet frame, world units — shared by the drawn
    rounded rectangle and the boundary-exit geometry so exits ride the
    visible frame line exactly. */
export const FRAME_CORNER_W = 8

export type BodyKind = 'term' | 'ref' | 'atom' | 'body' | 'end' | 'anchor'

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

// ---- the massless-elastica wire view-state (plan 22) -----------------------

/** A wire endpoint bound to a node port (the disc-edge rim anchor + the port
    normal are DERIVED from the body each evaluation — never stored). */
export type WireBind = { readonly body: string; readonly key: string }

/** A leg terminal. `bind i` = binds[i] (port rim + normal); `end` = the wire's
    single wire-owned END body (`endBodyId`) — the ∃ tip or the ∀ via — a FREE
    LEAF of the tree (no arrival-tangent constraint), reached with whatever
    tangent minimizes bend; `slot i` = the i-th incidence in the wire's `slots`
    list — a fixed point on the inner frame edge with the inward-normal arrival
    tangent (no body and no DOF). */
export type WireLegEnd =
  | { readonly kind: 'bind'; readonly i: number }
  | { readonly kind: 'end' }
  /** a wire-owned Steiner BRANCH point (index into `WireView.branches`): a k-ary
      junction is a TREE of these, its edges the ordinary elastica legs. */
  | { readonly kind: 'branch'; readonly i: number }
  | { readonly kind: 'slot'; readonly i: number }

/** One leg of a wire: the massless θ-quadratic from terminal `a` to terminal `b`.
    A junction leg's tangents at the branch points it touches are ORDINARY free
    DOFs (no trunk slaving): `angA` is the LEAVING travel direction at end `a`
    (honored exactly as θ(0)) and `angB` the ARRIVAL travel direction at end `b`
    (pulled to by the WELL_S arrival well). `angA` is live only when `a` is a
    Steiner BRANCH point (an internal tree edge); a bind/slot end fixes θ(0) to its
    port/slot normal, so `angA` is inert there. `angB` is live when `b` is a branch
    point; an `end` leaf is a FREE end (no arrival tangent, `angB` inert). Both are
    descended by the same gated angle step as every other DOF; `cache` memoizes the
    solve on the exact boundary tuple. */
export type WireLeg = {
  readonly a: WireLegEnd
  readonly b: WireLegEnd
  angA: number
  angB: number
  readonly cache: LegCache
}

/** A wire's complete view-state (plan 22/24): node-port binds, zero or more
    ordered boundary incidences, an optional wire-owned END body, and its tree.

    The junction state is literally (T, b, τ): `legs` are the tree EDGES (T) with
    their per-half-edge tangents (τ = `angA/angB`); `branches` are the internal
    branch-vertex POSITIONS (b). Nothing else — there is no 'junction' entity, no
    hub: where legs meet is downstream of which tree T the wire currently holds.

    Boundary incidence is positional, not a property unique to a wire: one line
    of identity may occupy several boundary positions. `slots[i]` is the logical
    boundary index named by a `{ kind: 'slot', i }` leg terminal. Topology is
    uniform: the tree's terminals are the port binds, the boundary slots, and the
    wire-owned END body (if any); one terminal needs no leg, two terminals form one
    direct elastica, and three or more form a Steiner tree of branch vertices. */
export type WireView = {
  readonly binds: WireBind[]
  /** The wire's single wire-owned END body id (the ∃ tip, the ∀ via, or a bare
      ∃ dot), or null. A free-end LEAF terminal of the tree (`{ kind: 'end' }`). */
  readonly endBodyId: string | null
  readonly slots: readonly number[]
  readonly legs: WireLeg[]
  /** b of (T, b, τ): the internal branch-vertex POSITIONS of the wire's tree (DOFs),
      in tree-index order (tree vertices are terminals 0..nT-1 then branches nT..).
      The tree edges are the ordinary elastica `legs`; the topology T that says which
      vertices each edge joins is CARRIED state (never re-derived from geometry) and
      changes only by a strict-descent face crossing (relax.ts `tryFaceCross`, the
      canonical φ). Empty for a plain 2-terminal wire or a bare ∃. */
  readonly branches: Vec2[]
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
  /** PLAN 22: every boundary wire and each >= 1-endpoint internal wire is a
      massless-elastica view (binds + optional hub/tip + derived legs) — see
      elastica.ts + relax.ts for the energy model. A bare boundary wire is a
      bodyless, zero-leg view at its fixed slot; only a bare internal wire is a
      homed body with no entry. */
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

/** The fixed proof frame: centre + half-extent of a near-square rounded box. */
export type StoredFrame = { readonly center: Vec2; readonly half: number }

/** Local anatomy scale per node kind — atoms and terms are drawn larger so
    their structure is legible against the wire rhythm. */
export function ascaleOf(kind: BodyKind): number {
  return kind === 'atom' ? 2.0 : kind === 'term' || kind === 'body' ? 1.4 : 1
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
    case 'atom':
      return atomGeometry(n.sig.args.length)
    case 'ref':
      return refGeometry(n.sig.args.length)
    case 'body':
      return bodyGeometry(n.content.boundary.length - n.sig.args.length)
  }
}

/** World-space anchor of (geometry, centre, port). */
export function anchorOf(geometry: NodeGeometry, center: Vec2, port: Port): Vec2 {
  if (port.kind === 'output') return add(center, geometry.outputAnchor)
  if (port.kind === 'head') {
    if (geometry.headAnchor === null) throw new Error('geometry has no head anchor for a head port')
    return add(center, geometry.headAnchor)
  }
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
  // seed BOTH end-tangent DOFs to the leg's chord direction (a straight leg): the
  // representable seed, and the rest value for an unobstructed junction leg.
  const mkLeg = (a: WireLegEnd, b: WireLegEnd, angle: number): WireLeg =>
    ({ a, b, angA: angle, angB: angle, cache: mkLegCache() })
  const chordAngle = (p: Vec2, q: Vec2): number => Math.atan2(q.y - p.y, q.x - p.x)

  // Build the wire's tree (T, b) over its terminals. `ends`/`pos` are the terminal
  // leg-ends and their world seed positions in tree order. Fewer than two terminals
  // draw nothing (a bare dot); two terminals are one direct elastica; three or more
  // are a soap-film Steiner tree of branch vertices (buildJunctionTree seeds T and b,
  // then strict descent + face crossings own them). A wire-owned END terminal is
  // oriented onto the leg's `b` side so it reads as a free leaf (no arrival tangent).
  const buildTree = (ends: readonly WireLegEnd[], pos: readonly Vec2[]): { legs: WireLeg[]; branches: Vec2[] } => {
    if (pos.length < 2) return { legs: [], branches: [] }
    if (pos.length === 2) return { legs: [mkLeg(ends[0]!, ends[1]!, chordAngle(pos[0]!, pos[1]!))], branches: [] }
    const built = buildJunctionTree(pos)
    const branches = built.branchPts
    const nT = pos.length
    const endOf = (node: number): WireLegEnd => node < nT ? ends[node]! : { kind: 'branch', i: node - nT }
    const posOf = (node: number): Vec2 => node < nT ? pos[node]! : branches[node - nT]!
    const legs = built.edges.map(([u, v]) => {
      const [a, b] = endOf(u).kind === 'end' ? [v, u] : [u, v] // an END terminal is the free leaf → put it at `b`
      return mkLeg(endOf(a), endOf(b), chordAngle(posOf(a), posOf(b)))
    })
    return { legs, branches }
  }

  for (const [wid, w] of Object.entries(d.wires)) {
    const binds: WireBind[] = w.endpoints.map((ep) => ({ body: ep.node, key: pkey(ep.port) }))
    const slots = slotsOf.get(wid) ?? []
    const isBoundary = slots.length > 0
    if (!isBoundary && binds.length === 0) {
      // A bare INTERNAL ∃ — the wire asserts only that an individual exists:
      // one scope-homed body, no legs (its dot is the whole rendering).
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
    const bindEnds = binds.map((_, k): WireLegEnd => ({ kind: 'bind', i: k }))

    let endBodyId: string | null = null
    let legs: WireLeg[] = []
    let branches: Vec2[] = []
    if (isBoundary) {
      // the tree's terminals are the port binds plus every boundary incidence (a fixed
      // frame slot). No wire-owned END body — the line exits to the frame.
      const c = centroid()
      const slotSeeds = slots.map((position) => {
        const angle = -Math.PI / 2 + (2 * Math.PI * position) / boundary.length
        return { x: c.x + 30 * Math.cos(angle), y: c.y + 30 * Math.sin(angle) }
      })
      const slotEnds = slots.map((_, si): WireLegEnd => ({ kind: 'slot', i: si }))
      const r = buildTree([...bindEnds, ...slotEnds], [...anchorPos, ...slotSeeds])
      legs = r.legs; branches = r.branches
    } else if (binds.length === 1) {
      // dangling ∃: one bind + a scope-homed END body (its loose tip) — a direct leaf.
      const b = mkWireBody(`j:${wid}`, w.scope, anchorPos[0]!)
      endBodyId = b.id
      const r = buildTree([{ kind: 'bind', i: 0 }, { kind: 'end' }], [anchorPos[0]!, b.pos])
      legs = r.legs; branches = r.branches
    } else if (w.scope !== w.endpoints
      .map((ep) => d.nodes[ep.node]!.region)
      .reduce((a, b) => deepestCommonAncestor(d, a, b))) {
      // the ∀ via-body: a scope-homed END body that is an ORDINARY LEAF TERMINAL of the
      // tree over {binds, via} (ruling A) — the line tributary-merges into it, no star hub.
      const b = mkWireBody(`x:${wid}`, w.scope, centroid())
      endBodyId = b.id
      const r = buildTree([...bindEnds, { kind: 'end' }], [...anchorPos, b.pos])
      legs = r.legs; branches = r.branches
    } else {
      // same scope, no ∀: a direct port-to-port leg (2 binds) or a pure k≥3 interior
      // junction — a Steiner tree over the ports.
      const r = buildTree(bindEnds, anchorPos)
      legs = r.legs; branches = r.branches
    }
    wires.set(wid, { binds, endBodyId, slots, legs, branches })
  }

  return engine
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
  for (const [id, nb] of next.bodies) {
    const pb = prev.bodies.get(id)
    if (pb === undefined) continue
    nb.pos = denorm(pb.pos, prev.scale)
    nb.theta = pb.theta
  }
  // A surviving wire carries its complete junction state (T, b, τ). The signature
  // matches wire IDENTITY — the terminal set (binds + END body presence + slots) — NOT
  // the branch count: the topology T is a coordinate the survivor carries, so the
  // count and adjacency come from the survivor, never from `next`'s fresh seed.
  const sig = (v: WireView): string =>
    [...v.binds.map((b) => `${b.body}:${b.key}`), v.endBodyId === null ? '-' : 'end', `slots:${v.slots.join(',')}`].join('|')
  for (const [wid, nv] of next.wires) {
    const pv = prev.wires.get(wid)
    if (pv === undefined || sig(pv) !== sig(nv)) continue
    // Carry the junction state (T, b, τ) VERBATIM from the survivor: T is the leg
    // end-structure (which terminals/branches each edge connects), b the branch
    // positions, τ the per-leg tangents. T is CARRIED, never re-derived from the
    // fresh soap-tree seed — so an achieved restructuring survives every rewrite
    // (kills diagnosed cause (a) structurally). Leg geometry stays memoryless: the
    // carried legs get a fresh cache and re-solve from their live boundary data.
    nv.branches.length = 0
    for (const p of pv.branches) nv.branches.push(denorm(p, prev.scale))
    nv.legs.length = 0
    for (const l of pv.legs) nv.legs.push({ a: l.a, b: l.b, angA: l.angA, angB: l.angB, cache: mkLegCache() })
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

    A ref discards its anatomy for a readable labelled disc drawn at DISC_R, so
    its wire meets that drawn rim at DISC_R along the port direction. An atom's
    ports sit on its rail rim and a term's ports sit on its drawn anatomy, so the
    wire meets that point directly — the port anchor is already on the drawing
    (ascale folded in). */
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
  // The fixed frame slot of a boundary wire: a point on the inner frame edge with
  // the OUTWARD frame normal (perpendicular meeting). A leg arriving at the slot
  // travels outward (+normal); a leg leaving the slot (the k≥2 slot arm) heads
  // inward (normal + π). Never a body, never a DOF.
  const slotAt = (end: Extract<WireLegEnd, { kind: 'slot' }>): FrameSlot | null =>
    resolvedFrameSlot(e, w.slots[end.i]!)
  // ENDPOINT POSITIONS + ownership first (a branch tangent needs the far position).
  const posOf = (end: WireLegEnd): { p: Vec2; own: string | null } => {
    switch (end.kind) {
      case 'slot': { const s = slotAt(end); return { p: s !== null ? s.point : { x: 0, y: 0 }, own: null } }
      case 'branch': return { p: w.branches[end.i]!, own: null }
      case 'end': return { p: e.bodies.get(w.endBodyId!)!.pos, own: null }
      case 'bind': { const bd = w.binds[end.i]!; return { p: worldBindAnchor(e, e.bodies.get(bd.body)!, bd.key), own: bd.body } }
    }
  }
  const A = posOf(leg.a), B = posOf(leg.b)
  const p0 = A.p, p1 = B.p, ownA = A.own, ownB = B.own
  // LEAVING tangent at terminal a (θ(0)): a port leaves along its rim normal; a
  // slot leaves inward; a Steiner BRANCH leaves along its own free tangent DOF
  // (`angA`) — an ordinary descended angle, no trunk slaving.
  let th0: number
  if (leg.a.kind === 'slot') { const s = slotAt(leg.a); th0 = (s !== null ? s.normal : 0) + Math.PI }
  else if (leg.a.kind === 'bind') { const bd = w.binds[leg.a.i]!; const b0 = e.bodies.get(bd.body)!; const la = b0.localAnchor.get(bd.key)!; th0 = Math.atan2(la.y, la.x) + b0.theta }
  else if (leg.a.kind === 'branch') { th0 = leg.angA }
  else { th0 = Math.atan2(p1.y - p0.y, p1.x - p0.x) }
  // ARRIVAL tangent at terminal b (travel INTO b): a branch arrival is the leg's own
  // free tangent DOF (`angB`), pulled to by the WELL_S well; a welled port/slot normal;
  // or a free wire-owned END leaf (∃ tip / ∀ via — no arrival tangent).
  let th1: number, freeEnd = false
  switch (leg.b.kind) {
    case 'end': th1 = 0; freeEnd = true; break
    case 'slot': { const s = slotAt(leg.b); th1 = s !== null ? s.normal : th0 + Math.PI; break }
    case 'branch': th1 = leg.angB; break
    case 'bind': { const bd = w.binds[leg.b.i]!; const b = e.bodies.get(bd.body)!; const la = b.localAnchor.get(bd.key)!; th1 = Math.atan2(la.y, la.x) + b.theta + Math.PI; break }
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
