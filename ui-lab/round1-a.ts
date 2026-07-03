/**
 * VARIANT A — "Toggle ledger" (the current model, made visible).
 * Click toggles an item in/out of the selection; empty click clears all.
 * Hover: thin outline of exactly what a click would hit, plus a readout
 * naming it. Selection: persistent amber rings. The baseline to beat.
 */
import { boot, hitShapes, sameHit, readout } from './shared'
import type { Hit } from '../src/app/hittest'

boot('Round 1 · A — toggle ledger', 'click toggles items in/out; empty click clears; hover outlines the hit', (lab) => {
  let hover: Hit | null = null
  const selected: Hit[] = []
  lab.canvas.addEventListener('pointermove', (e) => {
    hover = lab.hitAt(e.clientX, e.clientY)
    readout(hover ? lab.describe(hover) : '')
  })
  lab.canvas.addEventListener('pointerdown', (e) => {
    const h = lab.hitAt(e.clientX, e.clientY)
    if (h === null) { selected.length = 0; return }
    const i = selected.findIndex((s) => sameHit(s, h))
    if (i >= 0) selected.splice(i, 1)
    else selected.push(h)
  })
  lab.overlay((out) => {
    for (const s of selected) out.push(...hitShapes(lab, s, '#d97706', 2.5))
    if (hover && !selected.some((s) => sameHit(s, hover))) out.push(...hitShapes(lab, hover, '#2563eb', 1.8))
  })
})
