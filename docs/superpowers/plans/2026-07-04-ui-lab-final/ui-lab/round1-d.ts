/**
 * VARIANT D — "Brush". Press and DRAG paints items into the selection as the
 * cursor passes over them (nodes, wires, region rings alike); a plain click
 * still selects one; painting over an already-selected item UNPAINTS it;
 * empty click clears. Hover glows the item under the brush tip. Built for
 * gathering scattered wires/nodes without ceremony.
 */
import { boot, hitShapes, sameHit, readout } from './shared'
import type { Hit } from '../src/app/hittest'

boot('Round 1 · D — brush', 'drag paints items in (or out); click selects one; empty click clears', (lab) => {
  let hover: Hit | null = null
  let selected: Hit[] = []
  let brushing = false
  let brushErase = false
  let moved = false
  const applyBrush = (h: Hit | null) => {
    if (h === null) return
    const i = selected.findIndex((s) => sameHit(s, h))
    if (brushErase) { if (i >= 0) selected.splice(i, 1) }
    else if (i < 0) selected.push(h)
  }
  lab.canvas.addEventListener('pointermove', (e) => {
    hover = lab.hitAt(e.clientX, e.clientY)
    readout(hover ? lab.describe(hover) : '')
    if (brushing) { moved = true; applyBrush(hover) }
  })
  lab.canvas.addEventListener('pointerdown', (e) => {
    const h = lab.hitAt(e.clientX, e.clientY)
    brushing = true
    moved = false
    brushErase = h !== null && selected.some((s) => sameHit(s, h))
    if (h === null) { selected = []; brushing = false; return }
    applyBrush(h)
  })
  lab.canvas.addEventListener('pointerup', () => { brushing = false; void moved })
  lab.overlay((out) => {
    for (const s of selected) out.push(...hitShapes(lab, s, '#d97706', 2.5))
    if (hover && !selected.some((s) => sameHit(s, hover))) out.push(...hitShapes(lab, hover, '#2563eb', 1.8))
  })
})
