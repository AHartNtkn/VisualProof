// Round-3 design lab. New over round 2, per user rulings:
//  - SEMANTIC HONESTY: boundary wires exit through a visible sheet FRAME
//    (a loose end inside the sheet means ∃ and is drawn only for genuinely
//    internal wires). Goal-first labels.
//  - BRANCH JUNCTIONS: every ≥3-endpoint line of identity gets an explicit
//    junction body (relaxed like a node, contained in the wire's scope);
//    unary nodes therefore show exactly ONE leg.
//  - SATELLITE CONSTANTS: constant leaves hang OUTSIDE the λ-anatomy on a
//    short stem — geometry reserves the space; nothing paints over anatomy.
//  - UNIFORM DISCS: every named disc (relation refs and constants) has one
//    standard world-unit size.
import type { Diagram, DiagramNode, NodeId, Port, RegionId, WireId } from './src/kernel/diagram/diagram'
import { requiredPorts } from './src/kernel/diagram/diagram'
import type { Vec2 } from './src/view/vec'
import type { NodeGeometry } from './src/view/bend'
import { nodeGeometry, anchorOf } from './src/view/scene'
import { buildFregeTheory } from './src/theories/frege'

const TAU = Math.PI * 2
const DISC_R = 5.5          // standard named-disc radius (world units)
const SAT_STEM = 3.5        // satellite stem length beyond anatomy edge

// ---------- model ----------

type Satellite = { localPos: Vec2; discLocal: Vec2; label: string }

type Body = {
  readonly id: string
  readonly kind: 'term' | 'ref' | 'atom' | 'junction'
  readonly node: DiagramNode | null
  readonly geometry: NodeGeometry | null
  readonly localAnchor: Map<string, Vec2>
  readonly satellites: Satellite[]
  readonly discR: number
  readonly region: RegionId
  pos: Vec2
  vel: Vec2
  theta: number
}

type Leg = { from: { body: string; key: string | null }; to: { body: string; key: string | null } }
// key null = the body's center (junctions); frame legs handled separately

type Engine = {
  readonly d: Diagram
  readonly bodies: Map<string, Body>
  readonly childrenOf: Map<RegionId, RegionId[]>
  readonly membersOf: Map<RegionId, string[]>   // node/junction body ids per region
  readonly legs: Leg[]
  readonly boundaryOf: Map<WireId, string>       // boundary wire → its exit body id
  readonly boundary: readonly WireId[]
  regions: Map<RegionId, { center: Vec2; radius: number }>
}

function pkey(p: Port): string {
  return p.kind === 'output' ? 'out' : p.kind === 'freeVar' ? `v:${p.name}` : `a:${p.index}`
}

function mkEngine(d: Diagram, boundary: readonly WireId[]): Engine {
  const bodies = new Map<string, Body>()
  let i = 0
  for (const [id, n] of Object.entries(d.nodes)) {
    const g = nodeGeometry(d, id)
    const localAnchor = new Map<string, Vec2>()
    let anatomyR = 3
    const ascale = n.kind === 'atom' ? 2.0 : n.kind === 'term' ? 1.4 : 1
    for (const p of requiredPorts(d, n)) {
      const a0 = anchorOf(g, { x: 0, y: 0 }, p)
      const a = { x: a0.x * ascale, y: a0.y * ascale }
      localAnchor.set(pkey(p), a)
      anatomyR = Math.max(anatomyR, Math.hypot(a.x, a.y))
    }
    for (const arc of g.arcs) anatomyR = Math.max(anatomyR, arc.r)
    // satellites: constant leaves hang outside the anatomy on a stem
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
    for (const s of satellites) discR = Math.max(discR, Math.hypot(s.discLocal.x, s.discLocal.y) * (n.kind === 'term' ? 1.4 : 1) + DISC_R + 1.5)
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
    const ends = w.endpoints.map((ep) => ({ body: ep.node, key: pkey(ep.port) }))
    const needsJunction = ends.length + (bset.has(wid) ? 1 : 0) >= 3
    if (needsJunction) {
      const jid = `j:${wid}`
      bodies.set(jid, {
        id: jid, kind: 'junction', node: null, geometry: null,
        localAnchor: new Map(), satellites: [], discR: 4.5, region: w.scope,
        pos: { x: (i++) * 3, y: -(i * 2) }, vel: { x: 0, y: 0 }, theta: 0,
      })
      membersOf.get(w.scope)!.push(jid)
      for (const en of ends) legs.push({ from: { body: en.body, key: en.key }, to: { body: jid, key: null } })
      if (bset.has(wid)) boundaryOf.set(wid, jid)
    } else if (ends.length === 2) {
      legs.push({ from: ends[0]!, to: ends[1]! })
      if (bset.has(wid)) boundaryOf.set(wid, ends[0]!.body) // won't happen: 2 ends + boundary = junction
    } else if (ends.length === 1) {
      if (bset.has(wid)) boundaryOf.set(wid, ends[0]!.body)
      else legs.push({ from: ends[0]!, to: ends[0]! }) // genuine ∃ loose end, drawn as stub
    }
  }
  return { d, bodies, childrenOf, membersOf, legs, boundaryOf, boundary, regions: new Map() }
}

function worldAnchor(b: Body, key: string | null): Vec2 {
  if (key === null) return b.pos
  const a = b.localAnchor.get(key)!
  const c = Math.cos(b.theta), s = Math.sin(b.theta)
  return { x: b.pos.x + a.x * c - a.y * s, y: b.pos.y + a.x * s + a.y * c }
}

function portNormal(b: Body, key: string | null, toward: Vec2): number {
  if (key === null) return Math.atan2(toward.y - b.pos.y, toward.x - b.pos.x)
  const a = b.localAnchor.get(key)!
  return Math.atan2(a.y, a.x) + b.theta
}

// ---------- regions ----------

const REGION_PAD = 5
const SIB_GAP = 5

function recomputeRegions(e: Engine): void {
  const order: RegionId[] = []
  const visit = (rid: RegionId): void => { for (const c of e.childrenOf.get(rid)!) visit(c); order.push(rid) }
  visit(e.d.root)
  for (const rid of order) {
    const discs: { c: Vec2; r: number }[] = []
    for (const mid of e.membersOf.get(rid)!) {
      const b = e.bodies.get(mid)!
      discs.push({ c: b.pos, r: b.discR })
    }
    for (const c of e.childrenOf.get(rid)!) discs.push({ c: e.regions.get(c)!.center, r: e.regions.get(c)!.radius + REGION_PAD * 0.8 })
    if (discs.length === 0) { e.regions.set(rid, { center: { x: 0, y: 0 }, radius: 10 }); continue }
    // true minimal enclosing circle of the member discs: subgradient descent
    // on the convex objective f(c) = max_i (|c - c_i| + r_i)
    const center = { x: 0, y: 0 }
    for (const m of discs) { center.x += m.c.x; center.y += m.c.y }
    center.x /= discs.length; center.y /= discs.length
    for (let it = 0; it < 80; it++) {
      let worst = discs[0]!, worstV = -Infinity
      for (const m of discs) {
        const vv = Math.hypot(m.c.x - center.x, m.c.y - center.y) + m.r
        if (vv > worstV) { worstV = vv; worst = m }
      }
      const dx = worst.c.x - center.x, dy = worst.c.y - center.y
      const dd = Math.hypot(dx, dy)
      if (dd < 0.02) break
      const step = Math.min(dd, worstV * 0.6 / (it + 2))
      center.x += (dx / dd) * step
      center.y += (dy / dd) * step
    }
    let radius = 10
    for (const m of discs) radius = Math.max(radius, Math.hypot(m.c.x - center.x, m.c.y - center.y) + m.r + REGION_PAD)
    e.regions.set(rid, { center, radius })
  }
}

function shiftSubtree(e: Engine, rid: RegionId, dx: number, dy: number): void {
  for (const mid of e.membersOf.get(rid)!) {
    const b = e.bodies.get(mid)!
    b.pos = { x: b.pos.x + dx, y: b.pos.y + dy }
  }
  for (const c of e.childrenOf.get(rid)!) shiftSubtree(e, c, dx, dy)
}

function subtreeMembers(e: Engine, rid: RegionId): string[] {
  const out = [...e.membersOf.get(rid)!]
  for (const c of e.childrenOf.get(rid)!) out.push(...subtreeMembers(e, c))
  return out
}

function resolveOverlaps(e: Engine): boolean {
  let moved = false
  for (const rid of e.regions.keys()) {
    const items: { sub: RegionId | null; id: string; c: Vec2; r: number }[] = []
    for (const mid of e.membersOf.get(rid)!) {
      const b = e.bodies.get(mid)!
      items.push({ sub: null, id: mid, c: b.pos, r: b.discR })
    }
    for (const c of e.childrenOf.get(rid)!) {
      const g = e.regions.get(c)!
      items.push({ sub: c, id: c, c: g.center, r: g.radius })
    }
    for (let i = 0; i < items.length; i++) for (let j = i + 1; j < items.length; j++) {
      const A = items[i]!, B = items[j]!
      const dx = B.c.x - A.c.x, dy = B.c.y - A.c.y
      const dist = Math.hypot(dx, dy) || 0.001
      const need = A.r + B.r + SIB_GAP
      if (dist < need) {
        const push = (need - dist) / 2 + 0.1
        const ux = dx / dist, uy = dy / dist
        const move = (it: typeof A, sx: number, sy: number): void => {
          if (it.sub === null) {
            const b = e.bodies.get(it.id)!
            b.pos = { x: b.pos.x + sx, y: b.pos.y + sy }
          } else shiftSubtree(e, it.sub, sx, sy)
        }
        move(A, -ux * push, -uy * push)
        move(B, ux * push, uy * push)
        moved = true
      }
    }
  }
  if (moved) recomputeRegions(e)
  return moved
}

// ---------- relaxation ----------

function relax(e: Engine, ticks: number): void {
  const DT = 0.06, DAMP = 4, REP = 900, SPRING = 2.2, ROT_BLEND = 0.15
  for (let t = 0; t < ticks; t++) {
    recomputeRegions(e)
    const force = new Map<string, Vec2>()
    for (const id of e.bodies.keys()) force.set(id, { x: 0, y: 0 })
    for (const rid of e.regions.keys()) {
      const discs: { c: Vec2; r: number; mid?: string; sub?: RegionId }[] = []
      for (const mid of e.membersOf.get(rid)!) discs.push({ c: e.bodies.get(mid)!.pos, r: e.bodies.get(mid)!.discR, mid })
      for (const c of e.childrenOf.get(rid)!) discs.push({ c: e.regions.get(c)!.center, r: e.regions.get(c)!.radius, sub: c })
      for (let i = 0; i < discs.length; i++) for (let j = i + 1; j < discs.length; j++) {
        const A = discs[i]!, B = discs[j]!
        const dx = B.c.x - A.c.x, dy = B.c.y - A.c.y
        const dist = Math.max(Math.hypot(dx, dy), 1)
        const gap = dist - A.r - B.r
        const f = REP / Math.max(gap + 8, 4) ** 2
        const ux = dx / dist, uy = dy / dist
        const apply = (D: typeof A, sx: number, sy: number): void => {
          const targets = D.mid !== undefined ? [D.mid] : subtreeMembers(e, D.sub!)
          for (const mid of targets) { const F = force.get(mid)!; F.x += sx; F.y += sy }
        }
        apply(A, -ux * f, -uy * f)
        apply(B, ux * f, uy * f)
      }
    }
    // leg springs with a rest length: legs approach one spatial rhythm
    const REST = 18
    for (const leg of e.legs) {
      const A = e.bodies.get(leg.from.body)!, B = e.bodies.get(leg.to.body)!
      if (A === B) continue
      const pa = worldAnchor(A, leg.from.key), pb = worldAnchor(B, leg.to.key)
      const dx = pb.x - pa.x, dy = pb.y - pa.y
      const dist = Math.max(Math.hypot(dx, dy), 0.5)
      const f = SPRING * (dist - REST) / dist
      const FA = force.get(A.id)!, FB = force.get(B.id)!
      FA.x += dx * f; FA.y += dy * f
      FB.x -= dx * f; FB.y -= dy * f
    }
    // cohesion
    for (const rid of e.regions.keys()) {
      const mids = e.membersOf.get(rid)!
      const kids = e.childrenOf.get(rid)!
      if (mids.length + kids.length < 2) continue
      const cen = { x: 0, y: 0 }
      let m = 0
      for (const mid of mids) { const b = e.bodies.get(mid)!; cen.x += b.pos.x; cen.y += b.pos.y; m++ }
      for (const c of kids) { const g = e.regions.get(c)!; cen.x += g.center.x; cen.y += g.center.y; m++ }
      cen.x /= m; cen.y /= m
      for (const mid of mids) {
        const b = e.bodies.get(mid)!
        const F = force.get(mid)!
        F.x += (cen.x - b.pos.x) * 0.65; F.y += (cen.y - b.pos.y) * 0.65
      }
      for (const c of kids) {
        const g = e.regions.get(c)!
        const pull = { x: (cen.x - g.center.x) * 0.35, y: (cen.y - g.center.y) * 0.35 }
        for (const mid of subtreeMembers(e, c)) { const F = force.get(mid)!; F.x += pull.x; F.y += pull.y }
      }
    }
    for (const b of e.bodies.values()) {
      const F = force.get(b.id)!
      b.vel = { x: (b.vel.x + F.x * DT) / (1 + DAMP * DT), y: (b.vel.y + F.y * DT) / (1 + DAMP * DT) }
      b.pos = { x: b.pos.x + b.vel.x * DT, y: b.pos.y + b.vel.y * DT }
    }
    // rotation toward circular mean of leg-direction mismatches
    const legsByBody = new Map<string, { key: string; other: Body; otherKey: string | null }[]>()
    for (const leg of e.legs) {
      if (leg.from.key !== null) {
        if (!legsByBody.has(leg.from.body)) legsByBody.set(leg.from.body, [])
        legsByBody.get(leg.from.body)!.push({ key: leg.from.key, other: e.bodies.get(leg.to.body)!, otherKey: leg.to.key })
      }
      if (leg.to.key !== null) {
        if (!legsByBody.has(leg.to.body)) legsByBody.set(leg.to.body, [])
        legsByBody.get(leg.to.body)!.push({ key: leg.to.key, other: e.bodies.get(leg.from.body)!, otherKey: leg.from.key })
      }
    }
    // boundary exits contribute rotation torque: the exit body wants its
    // port normal aimed at its frame edge (approximated by current sheet box)
    const sheetG = e.regions.get(e.d.root)
    for (const [wid, bid] of e.boundaryOf) {
      const b = e.bodies.get(bid)!
      if (b.kind === 'junction' || sheetG === undefined) continue
      const w0 = e.d.wires[wid]!
      const key = pkey(w0.endpoints.find((ep) => ep.node === bid)!.port)
      const p = worldAnchor(b, key)
      const fr = sheetG.radius + 6
      const cand: Vec2[] = [
        { x: sheetG.center.x - fr, y: p.y }, { x: sheetG.center.x + fr, y: p.y },
        { x: p.x, y: sheetG.center.y - fr }, { x: p.x, y: sheetG.center.y + fr },
      ]
      let q = cand[0]!
      for (const c of cand) if (Math.hypot(c.x - p.x, c.y - p.y) < Math.hypot(q.x - p.x, q.y - p.y)) q = c
      if (!legsByBody.has(bid)) legsByBody.set(bid, [])
      legsByBody.get(bid)!.push({ key, other: { ...b, id: '__frame__', pos: q } as Body, otherKey: null })
    }
    for (const b of e.bodies.values()) {
      const ls = legsByBody.get(b.id)
      if (ls === undefined || ls.length === 0) continue
      let sinS = 0, cosS = 0
      for (const l of ls) {
        if (l.other.id === b.id) continue
        const q = worldAnchor(l.other, l.otherKey)
        const want = Math.atan2(q.y - b.pos.y, q.x - b.pos.x)
        const a = b.localAnchor.get(l.key)!
        const rest = Math.atan2(a.y, a.x)
        const delta = want - rest - b.theta
        sinS += Math.sin(delta); cosS += Math.cos(delta)
      }
      b.theta += Math.atan2(sinS, cosS) * ROT_BLEND
    }
    if (t % 10 === 0) resolveOverlaps(e)
  }
  recomputeRegions(e)
  for (let k = 0; k < 400 && resolveOverlaps(e); k++) { /* legal drawing */ }
}


// ---------- round 6: wire geometry candidates ----------

type WireMode = 'W1 Hobby' | 'W2 Escape-arc' | 'W3 Elastic chain' | 'W4 Straight+fillet'

type LegG = { pa: Vec2; ta: number; pb: Vec2; tb: number; skip: Set<string> }

/** Legs with junction-aware tangents: trunks flow tangent-continuously THROUGH branch points. */
function computeLegs(e: Engine): LegG[] {
  const byJunction = new Map<string, { leg: Leg; at: 'from' | 'to' }[]>()
  for (const leg of e.legs) {
    const fa = e.bodies.get(leg.from.body)!, tb2 = e.bodies.get(leg.to.body)!
    if (fa.kind === 'junction') {
      if (!byJunction.has(fa.id)) byJunction.set(fa.id, [])
      byJunction.get(fa.id)!.push({ leg, at: 'from' })
    }
    if (tb2.kind === 'junction') {
      if (!byJunction.has(tb2.id)) byJunction.set(tb2.id, [])
      byJunction.get(tb2.id)!.push({ leg, at: 'to' })
    }
  }
  const junctionTangent = new Map<string, Map<Leg, number>>()
  for (const [jid, ls] of byJunction) {
    const j = e.bodies.get(jid)!
    const dirs = ls.map(({ leg, at }) => {
      const otherEnd = at === 'from' ? leg.to : leg.from
      const ob = e.bodies.get(otherEnd.body)!
      const q = worldAnchor(ob, otherEnd.key)
      return Math.atan2(q.y - j.pos.y, q.x - j.pos.x)
    })
    let bi = 0, bj = 1, best = -Infinity
    for (let i = 0; i < dirs.length; i++) for (let k = i + 1; k < dirs.length; k++) {
      const diff = Math.atan2(Math.sin(dirs[i]! - dirs[k]!), Math.cos(dirs[i]! - dirs[k]!))
      const score = Math.abs(Math.abs(diff) - Math.PI) * -1 // closest to opposite wins
      if (score > best) { best = score; bi = i; bj = k }
    }
    const u = Math.atan2(
      Math.sin(dirs[bi]!) - Math.sin(dirs[bj]!),
      Math.cos(dirs[bi]!) - Math.cos(dirs[bj]!),
    )
    const m = new Map<Leg, number>()
    ls.forEach(({ leg }, idx) => {
      if (idx === bi) m.set(leg, u)
      else if (idx === bj) m.set(leg, u + Math.PI)
      else m.set(leg, dirs[idx]!)
    })
    junctionTangent.set(jid, m)
  }
  const out: LegG[] = []
  for (const leg of e.legs) {
    const A = e.bodies.get(leg.from.body)!, B = e.bodies.get(leg.to.body)!
    if (A === B && leg.from.key === leg.to.key) continue
    const pa = worldAnchor(A, leg.from.key), pb = worldAnchor(B, leg.to.key)
    const ta = A.kind === 'junction' ? junctionTangent.get(A.id)!.get(leg)! : portNormal(A, leg.from.key, pb)
    const tb = B.kind === 'junction' ? junctionTangent.get(B.id)!.get(leg)! : portNormal(B, leg.to.key, pa)
    out.push({ pa, ta, pb, tb, skip: new Set([A.id, B.id]) })
  }
  return out
}

/** Hobby's velocity function (METAFONT). */
function hobbyRho(theta: number, phi: number): number {
  const a = Math.sqrt(2), b = 1 / 16, c = (3 - Math.sqrt(5)) / 2
  const num = 2 + a * (Math.sin(theta) - b * Math.sin(phi)) * (Math.sin(phi) - b * Math.sin(theta)) * (Math.cos(theta) - Math.cos(phi))
  const den = 1 + (1 - c) * Math.cos(theta) + c * Math.cos(phi)
  return num / den
}

function drawHobbyLeg(ctx: CanvasRenderingContext2D, X: (p: Vec2) => Vec2, g: LegG): void {
  const chord = Math.atan2(g.pb.y - g.pa.y, g.pb.x - g.pa.x)
  const d = Math.hypot(g.pb.x - g.pa.x, g.pb.y - g.pa.y)
  const wrap = (x: number): number => Math.atan2(Math.sin(x), Math.cos(x))
  const theta = wrap(g.ta - chord)
  const phi = wrap(chord - (g.tb + Math.PI))
  const ra = Math.abs(hobbyRho(theta, phi)) * d / 3
  const rb = Math.abs(hobbyRho(phi, theta)) * d / 3
  const c1 = { x: g.pa.x + Math.cos(g.ta) * ra, y: g.pa.y + Math.sin(g.ta) * ra }
  const c2 = { x: g.pb.x + Math.cos(g.tb) * rb, y: g.pb.y + Math.sin(g.tb) * rb }
  const P = X(g.pa), C1 = X(c1), C2 = X(c2), Q = X(g.pb)
  ctx.beginPath(); ctx.moveTo(P.x, P.y)
  ctx.bezierCurveTo(C1.x, C1.y, C2.x, C2.y, Q.x, Q.y)
  ctx.stroke()
}

function drawEscapeArcLeg(ctx: CanvasRenderingContext2D, X: (p: Vec2) => Vec2, g: LegG): void {
  const d = Math.hypot(g.pb.x - g.pa.x, g.pb.y - g.pa.y)
  const esc = Math.min(7, d * 0.25)
  const ea = { x: g.pa.x + Math.cos(g.ta) * esc, y: g.pa.y + Math.sin(g.ta) * esc }
  const eb = { x: g.pb.x + Math.cos(g.tb) * esc, y: g.pb.y + Math.sin(g.tb) * esc }
  const mid = { x: (ea.x + eb.x) / 2, y: (ea.y + eb.y) / 2 }
  const k = Math.min(d * 0.3, 14)
  const c = {
    x: mid.x + (Math.cos(g.ta) - Math.cos(g.tb)) * k * 0.5,
    y: mid.y + (Math.sin(g.ta) - Math.sin(g.tb)) * k * 0.5,
  }
  const P = X(g.pa), EA = X(ea), C = X(c), EB = X(eb), Q = X(g.pb)
  ctx.beginPath(); ctx.moveTo(P.x, P.y); ctx.lineTo(EA.x, EA.y)
  ctx.quadraticCurveTo(C.x, C.y, EB.x, EB.y)
  ctx.lineTo(Q.x, Q.y)
  ctx.stroke()
}

function drawChainLeg(ctx: CanvasRenderingContext2D, X: (p: Vec2) => Vec2, e: Engine, g: LegG): void {
  const segs = 22
  const pts: Vec2[] = []
  for (let i = 0; i <= segs; i++) {
    const t = i / segs
    pts.push({ x: g.pa.x + (g.pb.x - g.pa.x) * t, y: g.pa.y + (g.pb.y - g.pa.y) * t })
  }
  const bodies = [...e.bodies.values()].filter((b) => b.kind !== 'junction' && !g.skip.has(b.id))
  for (let it = 0; it < 120; it++) {
    const d1 = Math.hypot(pts[1]!.x - pts[0]!.x, pts[1]!.y - pts[0]!.y)
    pts[1] = { x: pts[1]!.x + (pts[0]!.x + Math.cos(g.ta) * d1 - pts[1]!.x) * 0.5, y: pts[1]!.y + (pts[0]!.y + Math.sin(g.ta) * d1 - pts[1]!.y) * 0.5 }
    const dn = Math.hypot(pts[segs - 1]!.x - pts[segs]!.x, pts[segs - 1]!.y - pts[segs]!.y)
    pts[segs - 1] = { x: pts[segs - 1]!.x + (pts[segs]!.x + Math.cos(g.tb) * dn - pts[segs - 1]!.x) * 0.5, y: pts[segs - 1]!.y + (pts[segs]!.y + Math.sin(g.tb) * dn - pts[segs - 1]!.y) * 0.5 }
    for (let i = 1; i < segs; i++) {
      const p = pts[i]!
      let nx = p.x + ((pts[i - 1]!.x + pts[i + 1]!.x) / 2 - p.x) * 0.5
      let ny = p.y + ((pts[i - 1]!.y + pts[i + 1]!.y) / 2 - p.y) * 0.5
      for (const ob of bodies) {
        const dx = nx - ob.pos.x, dy = ny - ob.pos.y
        const dd = Math.hypot(dx, dy)
        const need = ob.discR + 2.5
        if (dd < need) {
          const s = dd < 0.001 ? { x: 1, y: 0 } : { x: dx / dd, y: dy / dd }
          nx = ob.pos.x + s.x * need
          ny = ob.pos.y + s.y * need
        }
      }
      pts[i] = { x: nx, y: ny }
    }
  }
  ctx.beginPath()
  const P0 = X(pts[0]!)
  ctx.moveTo(P0.x, P0.y)
  for (let i = 1; i <= segs; i++) { const P = X(pts[i]!); ctx.lineTo(P.x, P.y) }
  ctx.stroke()
}

function drawStraightLeg(ctx: CanvasRenderingContext2D, X: (p: Vec2) => Vec2, e: Engine, g: LegG): void {
  const esc = 3.5
  const ea = { x: g.pa.x + Math.cos(g.ta) * esc, y: g.pa.y + Math.sin(g.ta) * esc }
  const eb = { x: g.pb.x + Math.cos(g.tb) * esc, y: g.pb.y + Math.sin(g.tb) * esc }
  const pathPts: Vec2[] = [g.pa, ea]
  let via: Vec2 | null = null
  for (const ob of e.bodies.values()) {
    if (ob.kind === 'junction' || g.skip.has(ob.id)) continue
    const vx = eb.x - ea.x, vy = eb.y - ea.y
    const L2 = vx * vx + vy * vy
    if (L2 < 0.001) continue
    const t = Math.max(0, Math.min(1, ((ob.pos.x - ea.x) * vx + (ob.pos.y - ea.y) * vy) / L2))
    const cx = ea.x + vx * t, cy = ea.y + vy * t
    const dd = Math.hypot(cx - ob.pos.x, cy - ob.pos.y)
    if (dd < ob.discR + 2.5) {
      const s = dd < 0.001 ? { x: 1, y: 0 } : { x: (cx - ob.pos.x) / dd, y: (cy - ob.pos.y) / dd }
      via = { x: ob.pos.x + s.x * (ob.discR + 4), y: ob.pos.y + s.y * (ob.discR + 4) }
      break
    }
  }
  if (via !== null) pathPts.push(via)
  pathPts.push(eb, g.pb)
  ctx.beginPath()
  const P0 = X(pathPts[0]!)
  ctx.moveTo(P0.x, P0.y)
  for (let i = 1; i < pathPts.length; i++) { const P = X(pathPts[i]!); ctx.lineTo(P.x, P.y) }
  ctx.stroke()
}

// ---------- parametric painting ----------

type Style = {
  name: string
  canvas: string
  paper: string
  ink: string
  frame: string
  wire: string
  wireW: number
  negFill: string
  rimW: number
  discFill: string
  discText: string
  font: string
  sansLabels: boolean
  insetCuts: boolean
  insetColor: string
  discShadow: boolean
  wireGlow: boolean
  bubbleLightness: number
  junctionRing: boolean
}

function bubbleHues(d: Diagram, lightness: number): Map<RegionId, string> {
  const out = new Map<RegionId, string>()
  let k = 0
  for (const [rid, r] of Object.entries(d.regions)) {
    if (r.kind === 'bubble') {
      const hue = (268 + k * 137.5) % 360
      out.set(rid, `hsl(${hue.toFixed(0)}, 48%, ${lightness}%)`)
      k++
    }
  }
  return out
}

type View = { scale: number; ox: number; oy: number }

function paint(ctx: CanvasRenderingContext2D, e: Engine, w: number, h: number, st: Style, wireMode: WireMode): void {
  const hues = bubbleHues(e.d, st.bubbleLightness)
  const sheet = e.regions.get(e.d.root)!
  const frameR = sheet.radius + 6
  const minX = sheet.center.x - frameR, maxX = sheet.center.x + frameR
  const minY = sheet.center.y - frameR, maxY = sheet.center.y + frameR
  const pad = 18
  const scale = Math.max(2.0, Math.min(7.5, Math.min((w - 2 * pad) / (maxX - minX), (h - 2 * pad) / (maxY - minY))))
  const v: View = {
    scale,
    ox: pad - minX * scale + (w - 2 * pad - (maxX - minX) * scale) / 2,
    oy: pad - minY * scale + (h - 2 * pad - (maxY - minY) * scale) / 2,
  }
  const X = (p: Vec2): Vec2 => ({ x: p.x * v.scale + v.ox, y: p.y * v.scale + v.oy })

  ctx.fillStyle = st.canvas
  ctx.fillRect(0, 0, w, h)
  ctx.lineJoin = 'round'; ctx.lineCap = 'round'

  const F0 = X({ x: minX, y: minY }), F1 = X({ x: maxX, y: maxY })
  ctx.beginPath(); ctx.roundRect(F0.x, F0.y, F1.x - F0.x, F1.y - F0.y, 16)
  ctx.fillStyle = st.paper; ctx.fill()
  ctx.strokeStyle = st.frame; ctx.lineWidth = 2; ctx.stroke()

  const rs = [...e.regions.entries()]
    .filter(([rid]) => e.d.regions[rid]!.kind !== 'sheet')
    .sort((a, b) => b[1].radius - a[1].radius)
  const depth = (rid: RegionId): number => {
    let cur = rid, k = 0
    for (;;) {
      const r = e.d.regions[cur]!
      if (r.kind === 'sheet') return k
      if (r.kind === 'cut') k++
      cur = r.parent
    }
  }
  for (const [rid, g] of rs) {
    const kind = e.d.regions[rid]!.kind
    const c = X(g.center), R = g.radius * v.scale
    if (kind === 'bubble') {
      // the SO-quantifier ring glows in dark themes, matching its atoms
      if (st.wireGlow) { ctx.shadowColor = hues.get(rid)!; ctx.shadowBlur = 5 }
      ctx.beginPath(); ctx.arc(c.x, c.y, R, 0, TAU)
      ctx.strokeStyle = hues.get(rid)!; ctx.lineWidth = 2.0; ctx.stroke()
      ctx.shadowBlur = 0
      continue
    }
    ctx.beginPath(); ctx.arc(c.x, c.y, R, 0, TAU)
    ctx.fillStyle = depth(rid) % 2 === 1 ? st.negFill : st.paper
    ctx.fill()
    if (st.insetCuts) {
      const grad = ctx.createRadialGradient(c.x, c.y, R * 0.72, c.x, c.y, R)
      grad.addColorStop(0, 'rgba(0,0,0,0)')
      grad.addColorStop(1, st.insetColor)
      ctx.fillStyle = grad
      ctx.fill()
    }
    ctx.strokeStyle = st.ink; ctx.lineWidth = st.rimW; ctx.stroke()
  }

  // wires
  ctx.strokeStyle = st.wire
  ctx.lineWidth = st.wireW
  if (st.wireGlow) { ctx.shadowColor = st.wire; ctx.shadowBlur = 5 }
  const legsG = computeLegs(e)
  for (const g of legsG) {
    if (wireMode === 'W1 Hobby') drawHobbyLeg(ctx, X, g)
    else if (wireMode === 'W2 Escape-arc') drawEscapeArcLeg(ctx, X, g)
    else if (wireMode === 'W3 Elastic chain') drawChainLeg(ctx, X, e, g)
    else drawStraightLeg(ctx, X, e, g)
  }
  for (const leg of e.legs) {
    const A = e.bodies.get(leg.from.body)!, B = e.bodies.get(leg.to.body)!
    if (!(A === B && leg.from.key === leg.to.key)) continue
    const p = worldAnchor(A, leg.from.key)
    const n = portNormal(A, leg.from.key, { x: p.x + 1, y: p.y })
    const q = { x: p.x + Math.cos(n) * 10, y: p.y + Math.sin(n) * 10 }
    const P = X(p), Q = X(q)
    ctx.beginPath(); ctx.moveTo(P.x, P.y); ctx.lineTo(Q.x, Q.y); ctx.stroke()
    ctx.beginPath(); ctx.arc(Q.x, Q.y, 2.6, 0, TAU); ctx.fillStyle = st.wire; ctx.fill()
  }
  for (const [wid, bid] of e.boundaryOf) {
    const w0 = e.d.wires[wid]!
    const b = e.bodies.get(bid)!
    const anchorKey = b.kind === 'junction' ? null : pkey(w0.endpoints.find((ep) => ep.node === bid)!.port)
    const p = worldAnchor(b, anchorKey)
    const cand: Vec2[] = [
      { x: minX, y: p.y }, { x: maxX, y: p.y }, { x: p.x, y: minY }, { x: p.x, y: maxY },
    ]
    let q = cand[0]!
    for (const c of cand) if (Math.hypot(c.x - p.x, c.y - p.y) < Math.hypot(q.x - p.x, q.y - p.y)) q = c
    const horiz2 = q.x === minX || q.x === maxX
    const tb2 = horiz2 ? (q.x === minX ? Math.PI : 0) : (q.y === minY ? -Math.PI / 2 : Math.PI / 2)
    const ta2 = b.kind === 'junction' ? Math.atan2(q.y - p.y, q.x - p.x) : portNormal(b, anchorKey, q)
    const gLeg: LegG = { pa: p, ta: ta2, pb: q, tb: tb2 + Math.PI, skip: new Set([bid]) }
    if (wireMode === 'W3 Elastic chain') drawChainLeg(ctx, X, e, gLeg)
    else if (wireMode === 'W4 Straight+fillet') drawStraightLeg(ctx, X, e, gLeg)
    else drawHobbyLeg(ctx, X, gLeg)
    const Q = X(q)
    ctx.beginPath()
    if (horiz2) { ctx.moveTo(Q.x, Q.y - 5); ctx.lineTo(Q.x, Q.y + 5) } else { ctx.moveTo(Q.x - 5, Q.y); ctx.lineTo(Q.x + 5, Q.y) }
    ctx.stroke()
  }
  ctx.shadowBlur = 0
  for (const b of e.bodies.values()) {
    if (b.kind !== 'junction') continue
    const c = X(b.pos)
    if (st.junctionRing) {
      ctx.beginPath(); ctx.arc(c.x, c.y, 3.6, 0, TAU)
      ctx.fillStyle = st.paper; ctx.fill()
      ctx.beginPath(); ctx.arc(c.x, c.y, 2.6, 0, TAU)
      ctx.fillStyle = st.wire; ctx.fill()
    } else {
      ctx.beginPath(); ctx.arc(c.x, c.y, 3, 0, TAU)
      ctx.fillStyle = st.wire; ctx.fill()
    }
  }

  const disc = (cx: number, cy: number, R: number, label: string): void => {
    if (st.discShadow) { ctx.shadowColor = 'rgba(20,24,28,0.28)'; ctx.shadowBlur = 6; ctx.shadowOffsetY = 1.5 }
    ctx.beginPath(); ctx.arc(cx, cy, R, 0, TAU)
    ctx.fillStyle = st.discFill; ctx.fill()
    ctx.shadowBlur = 0; ctx.shadowOffsetY = 0
    ctx.strokeStyle = st.ink; ctx.lineWidth = 1.4; ctx.stroke()
    const label4 = label.length > 5 ? label.slice(0, 5) : label
    ctx.font = `600 ${Math.max(8.5, Math.min(14, R * 0.5))}px ${st.font}`
    ctx.textAlign = 'center'; ctx.textBaseline = 'middle'
    ctx.fillStyle = st.discText
    ctx.fillText(label4, cx, cy)
  }
  for (const b of e.bodies.values()) {
    if (b.kind === 'junction') continue
    const node = b.node!
    const c = X(b.pos)
    const S = v.scale
    if (node.kind === 'ref') {
      disc(c.x, c.y, DISC_R * S, node.defId)
      continue
    }
    ctx.save()
    ctx.translate(c.x, c.y)
    ctx.rotate(b.theta)
    const g = b.geometry!
    const ascale = node.kind === 'atom' ? 2.0 : node.kind === 'term' ? 1.4 : 1
    const atomHue = node.kind === 'atom' ? hues.get(node.binder)! : null
    // linework coherence: anatomy shares the wire's color and weight
    if (st.wireGlow) { ctx.shadowColor = atomHue ?? st.wire; ctx.shadowBlur = 4 }
    for (const a of g.arcs) {
      ctx.beginPath(); ctx.arc(0, 0, a.r * ascale * S, a.a0, a.a1)
      ctx.strokeStyle = atomHue ?? st.wire
      ctx.lineWidth = atomHue !== null ? st.wireW : st.wireW
      ctx.stroke()
    }
    for (const r of g.radials) {
      ctx.beginPath()
      ctx.moveTo(Math.cos(r.angle) * r.r0 * ascale * S, Math.sin(r.angle) * r.r0 * ascale * S)
      ctx.lineTo(Math.cos(r.angle) * r.r1 * ascale * S, Math.sin(r.angle) * r.r1 * ascale * S)
      ctx.strokeStyle = atomHue ?? st.wire
      ctx.lineWidth = st.wireW
      ctx.stroke()
    }
    if (node.kind === 'term') {
      if (g.exitArc !== null) {
        ctx.beginPath(); ctx.arc(0, 0, g.exitArc.r * ascale * S, g.exitArc.a0, g.exitArc.a1)
        ctx.strokeStyle = st.wire; ctx.lineWidth = st.wireW; ctx.stroke()
      }
      ctx.beginPath()
      ctx.moveTo(g.exitLine[0].x * ascale * S, g.exitLine[0].y * ascale * S)
      ctx.lineTo(g.exitLine[1].x * ascale * S, g.exitLine[1].y * ascale * S)
      ctx.strokeStyle = st.wire; ctx.lineWidth = st.wireW; ctx.stroke()
    }
    for (const s of b.satellites) {
      ctx.beginPath()
      ctx.moveTo(s.localPos.x * ascale * S, s.localPos.y * ascale * S)
      ctx.lineTo(s.discLocal.x * ascale * S, s.discLocal.y * ascale * S)
      ctx.strokeStyle = st.wire; ctx.lineWidth = st.wireW * 0.85; ctx.stroke()
    }
    ctx.shadowBlur = 0
    ctx.restore()
    for (const s of b.satellites) {
      const cs = Math.cos(b.theta), sn = Math.sin(b.theta)
      const asc2 = b.kind === 'term' ? 1.4 : 1
      const wp = { x: b.pos.x + s.discLocal.x * asc2 * cs - s.discLocal.y * asc2 * sn, y: b.pos.y + s.discLocal.x * asc2 * sn + s.discLocal.y * asc2 * cs }
      const W = X(wp)
      disc(W.x, W.y, DISC_R * 0.82 * S, s.label)
    }
  }
}

// ---------- page ----------

const STYLES: Style[] = [
  {
    name: 'Light (Manuscript)', canvas: '#e8e4d8', paper: '#faf7ee', ink: '#2a2118', frame: '#7a7263',
    wire: '#26343a', wireW: 2.2, negFill: 'rgba(90, 78, 58, 0.12)', rimW: 1.3,
    discFill: '#fffdf6', discText: '#2a2118', font: 'Georgia, serif', sansLabels: false,
    insetCuts: true, insetColor: 'rgba(58, 48, 32, 0.13)', discShadow: false, wireGlow: false,
    bubbleLightness: 46, junctionRing: true,
  },
  {
    name: 'Dark (Slate)', canvas: '#0e1013', paper: '#1c2026', ink: '#e6e1d6', frame: '#4a5058',
    wire: '#5bd2de', wireW: 2.2, negFill: 'rgba(255, 255, 255, 0.06)', rimW: 1.2,
    discFill: '#262c33', discText: '#eae5da', font: 'Georgia, serif', sansLabels: false,
    insetCuts: true, insetColor: 'rgba(0, 0, 0, 0.32)', discShadow: false, wireGlow: true,
    bubbleLightness: 64, junctionRing: true,
  },
]

const CELL_W = 888, CELL_H = 560

function addCell(title: string, run: (ctx: CanvasRenderingContext2D) => void): void {
  const cell = document.createElement('div'); cell.className = 'cell'
  const h2 = document.createElement('h2'); h2.textContent = title
  const canvas = document.createElement('canvas'); canvas.width = CELL_W; canvas.height = CELL_H
  cell.append(h2, canvas)
  document.getElementById('grid')!.append(cell)
  run(canvas.getContext('2d')!)
}

const theory = buildFregeTheory()
const plusComm = theory.theorems.find((t) => t.name === 'plusComm')!
const succShiftS = theory.theorems.find((t) => t.name === 'succShiftS')!
const natBody = theory.relations['nat']!

const cases: [string, Diagram, readonly WireId[]][] = [
  ['plusComm — ℕ(a) ∧ ℕ(b) ∧ (a+b = b+a)', plusComm.rhs.diagram, plusComm.rhs.boundary],
  ['ℕ definition body', natBody.diagram, natBody.boundary],
  ['succShiftS', succShiftS.rhs.diagram, succShiftS.rhs.boundary],
]

for (const [name, d, boundary] of cases) {
  const e = mkEngine(d, boundary)
  relax(e, 2600)
  for (const st of STYLES) {
    addCell(`${name} — ${st.name}`, (ctx) => paint(ctx, e, CELL_W, CELL_H, st, 'W1 Hobby'))
  }
}

document.getElementById('status')!.textContent =
  'render lab — round 8: the two first-class themes (unified linework, inset wells, Hobby wires)'
;(window as unknown as { __renderDone: boolean }).__renderDone = true
