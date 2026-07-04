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
export type Terminal = { p: Vec2; tangent: number }
export type MWire = { wid: WireId; hub: Body; terminals: Terminal[] }

export function collectMultiport(e: Engine): MWire[] {
  const groups = new Map<string, { wid: WireId; terminals: Terminal[] }>()
  for (const g of computeLegs(e)) {
    const A = e.bodies.get(g.leg.from.body)!
    const B = e.bodies.get(g.leg.to.body)!
    const hub = A.id === `j:${g.leg.wid}` ? A : B.id === `j:${g.leg.wid}` ? B : null
    if (hub === null) continue
    const term: Terminal = hub === A ? { p: g.pb, tangent: g.tb } : { p: g.pa, tangent: g.ta }
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

/** A short entry curve out of a terminal port: keeps the port-normal tangent
    so branches blend into the anatomy the way production legs do. */
export function entryCurve(t: Terminal, to: Vec2, stroke: string, width: number, glow: string | null): Shape {
  const dir = Math.atan2(to.y - t.p.y, to.x - t.p.x)
  const path = hobbyBezier(t.p, t.tangent, to, dir + Math.PI)
  return { kind: 'bezier', from: path.from, c1: path.c1, c2: path.c2, to: path.to, stroke, width, glow }
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

export { boot }
