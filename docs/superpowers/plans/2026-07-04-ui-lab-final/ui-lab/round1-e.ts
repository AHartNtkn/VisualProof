/**
 * VARIANT E — the Round-1 composite verdict: D's brush (drag paints in/out,
 * click toggles one, empty click clears) with hover that NEVER goes silent.
 * Hover on an unselected item: blue tint (nodes/regions) or blue stroke
 * (wires) — the would-be catch. Hover on a SELECTED item: its amber darkens —
 * dark-amber tint on nodes/regions, a wider dark-amber restroke on wires — so
 * selected things (wires especially) still answer the cursor.
 */
import { boot, installBrush } from './shared'

boot('Round 1 · E — brush, hover-aware', 'drag paints in/out; click toggles one; hover darkens selected things too', (lab) => {
  installBrush(lab)
})
