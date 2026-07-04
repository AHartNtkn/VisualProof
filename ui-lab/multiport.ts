/**
 * MULTIPORT WIRE RENDERING — shared plumbing for the round-8 demos.
 *
 * Today a ≥3-endpoint wire is a STAR: every leg runs to one central junction
 * body. The literature on drawing one k-adic connection ("edge standard"
 * hyperedge drawing) offers genuinely different shapes whose BRANCHES respond
 * to the layout's energy:
 *  - Steiner / soap-film trees: minimal networks; free degree-3 branch points
 *    settle at 120° junctions under uniform tension (Plateau's laws).
 *  - Force-directed edge bundling (Holten & van Wijk 2009): legs are flexible
 *    springs that ATTRACT each other; trunks emerge, no explicit junctions.
 *  - Flux/spiral trees (Buchin, Speckmann, Verbeek): branches merge
 *    tangentially along angle-restricted spirals toward a root — smooth
 *    tributary confluence.
 * Each variant page substitutes the painter's wire pass for multiport wires
 * only; 1–2 endpoint wires, stubs, and boundary exits keep today's rendering.
 * View-only throughout (layer law): nothing here touches the diagram.
 */
import { boot, type LabCtx } from './shared'
import { DiagramBuilder } from '../src/kernel/diagram/builder'
import type { Diagram, WireId } from '../src/kernel/diagram/diagram'
import { parseTerm } from '../src/kernel/term/parse'
import type { Body, Engine } from '../src/view/engine'
import { computeLegs, hobbyBezier, boundaryExits, existentialStubs, legPaths } from '../src/view/wires'
import type { Shape, Theme } from '../src/view/paint'
import { frameBounds, frameSlots } from '../src/view/engine'
import type { Vec2 } from '../src/view/vec'

// ---- the showcase: three refs sharing a 3-way and a 4-way line, a 5-way
// line reaching through a cut, a term with free ports on a shared line, and
// ordinary 1–2 endpoint wires for contrast
export function mkMultiportStart(): { d: Diagram; boundary: WireId[] } {
  const b = new DiagramBuilder()
  const root = b.root
  const plus = b.ref(root, 'plus', 3)
  const times = b.ref(root, 'times', 3)
  const succ = b.ref(root, 'succ', 2)
  const nat = b.ref(root, 'nat', 2)
  const zero = b.ref(root, 'zero', 1)
  const term = b.termNode(root, parseTerm('\\x. f (g x)'))
  b.wire(root, [
    { node: plus, port: { kind: 'arg', index: 0 } },
    { node: times, port: { kind: 'arg', index: 0 } },
    { node: succ, port: { kind: 'arg', index: 0 } },
  ])
  b.wire(root, [
    { node: plus, port: { kind: 'arg', index: 1 } },
    { node: times, port: { kind: 'arg', index: 1 } },
    { node: succ, port: { kind: 'arg', index: 1 } },
    { node: nat, port: { kind: 'arg', index: 0 } },
  ])
  const cut = b.cut(root)
  const lt = b.ref(cut, 'lt', 2)
  const sum = b.ref(cut, 'sum', 3)
  b.wire(cut, [
    { node: lt, port: { kind: 'arg', index: 0 } },
    { node: sum, port: { kind: 'arg', index: 0 } },
    { node: sum, port: { kind: 'arg', index: 2 } },
  ])
  // five ends spanning the cut boundary: junction homes at the dca (root)
  b.wire(root, [
    { node: plus, port: { kind: 'arg', index: 2 } },
    { node: times, port: { kind: 'arg', index: 2 } },
    { node: zero, port: { kind: 'arg', index: 0 } },
    { node: lt, port: { kind: 'arg', index: 1 } },
    { node: term, port: { kind: 'freeVar', name: 'f' } },
  ])
  // a plain 2-ender for contrast
  b.wire(root, [
    { node: nat, port: { kind: 'arg', index: 1 } },
    { node: term, port: { kind: 'freeVar', name: 'g' } },
  ])
  return { d: b.build(), boundary: [] }
}

// ---- multiport extraction: the hub body and the terminal ends of every
// ≥3-legged junction (endpoint anchors AND the scope-∃ dangle both count)
export type Terminal = { p: Vec2; tangent: number; body: string; key: string | null }
export type MWire = { wid: WireId; hub: Body; terminals: Terminal[] }

export function collectMultiport(e: Engine): MWire[] {
  const groups = new Map<string, { wid: WireId; terminals: Terminal[] }>()
  for (const g of computeLegs(e)) {
    const A = e.bodies.get(g.leg.from.body)!
    const B = e.bodies.get(g.leg.to.body)!
    const hub = A.id === `j:${g.leg.wid}` ? A : B.id === `j:${g.leg.wid}` ? B : null
    if (hub === null) continue
    const term: Terminal = hub === A
      ? { p: g.pb, tangent: g.tb, body: g.leg.to.body, key: g.leg.to.key }
      : { p: g.pa, tangent: g.ta, body: g.leg.from.body, key: g.leg.from.key }
    let entry = groups.get(hub.id)
    if (entry === undefined) { entry = { wid: g.leg.wid, terminals: [] }; groups.set(hub.id, entry) }
    entry.terminals.push(term)
  }
  const out: MWire[] = []
  for (const [hubId, { wid, terminals }] of groups) {
    if (terminals.length < 3) continue
    out.push({ wid, hub: e.bodies.get(hubId)!, terminals })
  }
  return out
}

/** The default wire pass with the given wires' legs, junction dots omitted
    (their rendering is the variant's job). Stubs, exits, and the frame pip
    keep the production behavior. */
export function basePaintExcept(e: Engine, st: Theme, skip: ReadonlySet<WireId>): Shape[] {
  const glow = (c: string): string | null => (st.wireGlow ? c : null)
  const shapes: Shape[] = []
  for (const { wid, path } of legPaths(e)) {
    if (skip.has(wid)) continue
    shapes.push({ kind: 'bezier', from: path.from, c1: path.c1, c2: path.c2, to: path.to, stroke: st.wire, width: st.wireW, glow: glow(st.wire) })
  }
  for (const s of existentialStubs(e)) {
    shapes.push({ kind: 'stub', from: s.from, to: s.to, dot: s.dot, dotRpx: 3, stroke: st.wire, width: st.wireW, glow: glow(st.wire) })
  }
  for (const ex of boundaryExits(e)) {
    shapes.push({ kind: 'exit', from: ex.path.from, c1: ex.path.c1, c2: ex.path.c2, to: ex.path.to, tick: ex.tick, stroke: st.wire, width: st.wireW, glow: glow(st.wire) })
  }
  const fb = frameBounds(e)
  if (fb !== null && e.boundary.length >= 2) {
    const s0 = frameSlots(fb, e.boundary.length)[0]!.point
    shapes.push({ kind: 'dot', center: s0, rPx: 2.6, fill: st.ink })
  }
  for (const b of e.bodies.values()) {
    if (b.kind !== 'junction') continue
    if (skip.has(b.id.slice(2) as WireId)) continue
    shapes.push({ kind: 'dot', center: b.pos, rPx: 4.4, fill: st.paper })
    shapes.push({ kind: 'dot', center: b.pos, rPx: 2.2, fill: st.wire })
  }
  return shapes
}

/** Direct body dragging for the render demos: grab any node and shove it —
    the branches must respond live. (No brush here: its wire hover overlay
    draws the production star, which would lie about these renderings.) */
export function installDrag(lab: LabCtx): void {
  let grab: { id: string; dx: number; dy: number } | null = null
  lab.canvas.addEventListener('pointerdown', (ev) => {
    const h = lab.hitAt(ev.clientX, ev.clientY)
    if (h === null || h.kind !== 'node') return
    const b = lab.engine.bodies.get(h.id)
    if (b === undefined) return
    const w = lab.toWorld(ev.clientX, ev.clientY)
    grab = { id: h.id, dx: b.pos.x - w.x, dy: b.pos.y - w.y }
    lab.canvas.setPointerCapture(ev.pointerId)
  })
  lab.canvas.addEventListener('pointermove', (ev) => {
    if (grab === null) return
    const b = lab.engine.bodies.get(grab.id)
    if (b === undefined) return
    const w = lab.toWorld(ev.clientX, ev.clientY)
    b.pos.x = w.x + grab.dx
    b.pos.y = w.y + grab.dy
    b.vel.x = 0
    b.vel.y = 0
  })
  lab.canvas.addEventListener('pointerup', () => { grab = null })
}

// ---- the soap-film Steiner machinery (round8-a verdict: acceptable with
// tweaks; shared by the straight-segment and tributary renderings).
// Free internal points relax under UNIT tension per incident branch
// (surface tension → 120° Plateau junctions) plus a KEEP-OUT from node
// discs: a branch point that settles behind a disc obscures the connection
// structure (USER report), so discs repel internal points from a radius
// where the wire would anyway have entered through a port. Spawn/merge
// distances are a hysteresis pair — they must be separated or the topology
// flaps every frame.
export type SoapTree = { pts: Vec2[]; adj: number[][]; nT: number }

const SPAWN_DIST = 1.0
const MERGE_DIST = 0.3
const TENSION_STEP = 0.25
const COS120 = Math.cos((2 * Math.PI) / 3)

export type Obstacle = { pos: Vec2; r: number }

export function nodeObstacles(e: Engine): Obstacle[] {
  const out: Obstacle[] = []
  for (const b of e.bodies.values()) {
    if (b.kind === 'junction' || b.kind === 'anchor') continue
    out.push({ pos: b.pos, r: b.discR + 1 })
  }
  return out
}

/** Terminal tangent against an ACTUAL target: real ports keep their anatomy
    normal (rotation relaxation turns the body); free-floating ends (the ∃
    dangle, key null) aim at the tree point they attach to — computeLegs
    aimed them at the production hub, which these renderings replace. */
export function terminalTangent(t: Terminal, toward: Vec2): number {
  return t.key === null ? Math.atan2(toward.y - t.p.y, toward.x - t.p.x) : t.tangent
}

/** Drive the production hub body to the tree's interior so the engine's
    ROTATION relaxation turns every node's port toward the drawn structure
    (with a stranded hub, ports face the wrong way and entry curves loop). */
export function driveHub(hub: Body, t: SoapTree): void {
  let n = 0, cx = 0, cy = 0
  for (let v = t.nT; v < t.pts.length; v++) {
    if (t.adj[v]!.length === 0) continue
    cx += t.pts[v]!.x
    cy += t.pts[v]!.y
    n++
  }
  if (n === 0) return
  hub.pos.x += (cx / n - hub.pos.x) * 0.2
  hub.pos.y += (cy / n - hub.pos.y) * 0.2
  hub.vel.x = 0
  hub.vel.y = 0
}

export function mkSoapTree(terminals: readonly Terminal[], hubPos: Vec2): SoapTree {
  const pts = terminals.map((x) => ({ ...x.p }))
  pts.push({ ...hubPos })
  return { pts, adj: [...terminals.map(() => [terminals.length]), terminals.map((_, i) => i)], nT: terminals.length }
}

export function relaxSoap(t: SoapTree, obstacles: readonly Obstacle[]): void {
  for (let iter = 0; iter < 6; iter++) {
    for (let v = t.nT; v < t.pts.length; v++) {
      let fx = 0, fy = 0
      for (const n of t.adj[v]!) {
        const dx = t.pts[n]!.x - t.pts[v]!.x, dy = t.pts[n]!.y - t.pts[v]!.y
        const d = Math.hypot(dx, dy)
        if (d < 1e-9) continue
        fx += dx / d
        fy += dy / d
      }
      for (const o of obstacles) {
        const dx = t.pts[v]!.x - o.pos.x, dy = t.pts[v]!.y - o.pos.y
        const d = Math.hypot(dx, dy)
        if (d >= o.r || d < 1e-9) continue
        const push = (o.r - d) / o.r // full tension-strength at the center, zero at the rim
        fx += (dx / d) * push * 2
        fy += (dy / d) * push * 2
      }
      t.pts[v] = { x: t.pts[v]!.x + fx * TENSION_STEP, y: t.pts[v]!.y + fy * TENSION_STEP }
    }
  }
}

export function reshapeSoap(t: SoapTree): void {
  // SPLIT: a branch point holding two branches tighter than 120° sheds them
  for (let v = t.nT; v < t.pts.length; v++) {
    const nbrs = t.adj[v]!
    if (nbrs.length < 4) continue
    let bi = -1, bj = -1, best = COS120
    for (let i = 0; i < nbrs.length; i++) for (let j = i + 1; j < nbrs.length; j++) {
      const a = t.pts[nbrs[i]!]!, b = t.pts[nbrs[j]!]!
      const ua = { x: a.x - t.pts[v]!.x, y: a.y - t.pts[v]!.y }
      const ub = { x: b.x - t.pts[v]!.x, y: b.y - t.pts[v]!.y }
      const la = Math.hypot(ua.x, ua.y), lb = Math.hypot(ub.x, ub.y)
      if (la < 1e-9 || lb < 1e-9) continue
      const cos = (ua.x * ub.x + ua.y * ub.y) / (la * lb)
      if (cos > best) { best = cos; bi = i; bj = j }
    }
    if (bi < 0) continue
    const a = nbrs[bi]!, b = nbrs[bj]!
    const dir = Math.atan2(
      (t.pts[a]!.y + t.pts[b]!.y) / 2 - t.pts[v]!.y,
      (t.pts[a]!.x + t.pts[b]!.x) / 2 - t.pts[v]!.x,
    )
    const w = t.pts.length
    t.pts.push({ x: t.pts[v]!.x + Math.cos(dir) * SPAWN_DIST, y: t.pts[v]!.y + Math.sin(dir) * SPAWN_DIST })
    t.adj.push([a, b, v])
    t.adj[v] = nbrs.filter((n) => n !== a && n !== b)
    t.adj[v]!.push(w)
    for (const x of [a, b]) t.adj[x] = t.adj[x]!.map((n) => (n === v ? w : n))
  }
  // MERGE: an internal edge that tension collapsed folds back into one point
  for (let v = t.nT; v < t.pts.length; v++) {
    for (const w of [...t.adj[v]!]) {
      if (w < t.nT || w <= v) continue
      const d = Math.hypot(t.pts[w]!.x - t.pts[v]!.x, t.pts[w]!.y - t.pts[v]!.y)
      if (d >= MERGE_DIST) continue
      t.adj[v] = [...t.adj[v]!.filter((n) => n !== w), ...t.adj[w]!.filter((n) => n !== v)]
      for (const n of t.adj[w]!) if (n !== v) t.adj[n] = t.adj[n]!.map((m) => (m === w ? v : m))
      t.adj[w] = []
      return
    }
  }
}

export { boot }
