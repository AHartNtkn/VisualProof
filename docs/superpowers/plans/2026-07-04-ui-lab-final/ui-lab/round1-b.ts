/**
 * VARIANT B — "Desktop standard". Click REPLACES the selection with the hit;
 * shift-click adds/removes; empty click clears; drag on empty space sweeps a
 * MARQUEE that selects every node/region whose disc lies inside. Hover: the
 * would-be hit brightens (fill tint, not just a ring).
 */
import { boot, hitShapes, sameHit, readout } from './shared'
import type { Hit } from '../src/app/hittest'
import type { Shape } from '../src/view/paint'

boot('Round 1 · B — desktop standard', 'click replaces; shift adds; drag on empty = marquee; hover tints', (lab) => {
  let hover: Hit | null = null
  let selected: Hit[] = []
  let marquee: { x0: number; y0: number; x1: number; y1: number } | null = null
  lab.canvas.addEventListener('pointermove', (e) => {
    if (marquee) { marquee.x1 = e.clientX; marquee.y1 = e.clientY; return }
    hover = lab.hitAt(e.clientX, e.clientY)
    readout(hover ? lab.describe(hover) : '')
  })
  lab.canvas.addEventListener('pointerdown', (e) => {
    const h = lab.hitAt(e.clientX, e.clientY)
    if (h === null) { marquee = { x0: e.clientX, y0: e.clientY, x1: e.clientX, y1: e.clientY }; if (!e.shiftKey) selected = []; return }
    if (e.shiftKey) {
      const i = selected.findIndex((s) => sameHit(s, h))
      if (i >= 0) selected.splice(i, 1); else selected.push(h)
    } else selected = [h]
  })
  lab.canvas.addEventListener('pointerup', () => {
    if (!marquee) return
    const a = lab.toWorld(Math.min(marquee.x0, marquee.x1), Math.min(marquee.y0, marquee.y1))
    const b = lab.toWorld(Math.max(marquee.x0, marquee.x1), Math.max(marquee.y0, marquee.y1))
    for (const [id, body] of lab.engine.bodies) {
      if (body.kind === 'junction' || body.kind === 'anchor') continue
      if (body.pos.x > a.x && body.pos.x < b.x && body.pos.y > a.y && body.pos.y < b.y) {
        const h: Hit = { kind: 'node', id }
        if (!selected.some((s) => sameHit(s, h))) selected.push(h)
      }
    }
    marquee = null
  })
  lab.overlay((out) => {
    for (const s of selected) out.push(...hitShapes(lab, s, '#d97706', 2.8))
    if (hover && !selected.some((x) => sameHit(x, hover))) {
      // tint = translucent fill over the hit disc/region; wires get the stroke
      if (hover.kind === 'node') {
        const b2 = lab.engine.bodies.get(hover.id)
        if (b2) out.push({ kind: 'circle', center: b2.pos, r: b2.discR, fill: '#2563eb22', stroke: null, width: 0, insetColor: null, glow: null } as Shape)
      } else if (hover.kind === 'region') {
        const g = lab.engine.regions.get(hover.id)
        if (g) out.push({ kind: 'circle', center: g.center, r: g.radius, fill: '#2563eb14', stroke: null, width: 0, insetColor: null, glow: null } as Shape)
      } else out.push(...hitShapes(lab, hover, '#2563eb', 1.8))
    }
    if (marquee) {
      const a = lab.toWorld(marquee.x0, marquee.y0), b2 = lab.toWorld(marquee.x1, marquee.y1)
      out.push({ kind: 'frame', x: Math.min(a.x, b2.x), y: Math.min(a.y, b2.y), w: Math.abs(b2.x - a.x), h: Math.abs(b2.y - a.y), cornerW: 1, fill: '#2563eb10', stroke: '#2563eb', width: 1 } as Shape)
    }
  })
})
