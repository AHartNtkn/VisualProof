/**
 * WIRE-PHYSICS demo plumbing: the showcase diagram and direct dragging.
 * All the view-side soap machinery that used to live here was PROMOTED
 * into the engine by plan 21 (src/view/wirechain.ts + relax.ts) — the
 * demo pages render the engine itself.
 */
import { boot, type LabCtx } from './shared'
import { DiagramBuilder } from '../src/kernel/diagram/builder'
import type { Diagram, WireId } from '../src/kernel/diagram/diagram'
import { parseTerm } from '../src/kernel/term/parse'

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
    // EXTENT LEASH (USER): components must never be dragged so far apart
    // that the fit-to-view zoom makes the diagram imperceivably small.
    // The grabbed body is held within 110% of the rest's bounding radius.
    let cx = 0, cy = 0, n = 0
    for (const [id, ob] of lab.engine.bodies) {
      if (id === grab.id) continue
      cx += ob.pos.x; cy += ob.pos.y; n++
    }
    if (n > 0) {
      cx /= n; cy /= n
      let rad = 0
      for (const [id, ob] of lab.engine.bodies) {
        if (id === grab.id) continue
        rad = Math.max(rad, Math.hypot(ob.pos.x - cx, ob.pos.y - cy) + ob.discR)
      }
      const leash = Math.max(20, rad * 1.1)
      const d = Math.hypot(b.pos.x - cx, b.pos.y - cy)
      if (d > leash) {
        b.pos.x = cx + ((b.pos.x - cx) / d) * leash
        b.pos.y = cy + ((b.pos.y - cy) / d) * leash
      }
    }
  })
  lab.canvas.addEventListener('pointerup', () => { grab = null })
}

export { boot }
