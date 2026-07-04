/**
 * WIRE PHYSICS (plan 21) — the engine itself, no view-side machinery.
 * Wires are first-class physical objects: chains/trees of wire-points
 * descending ONE energy (tension + bend + symmetric disc barriers), ports
 * pinned with perpendicular exits, junctions as free Plateau points, ∃/∀
 * ends as homed wire-owned bodies. Everything drawn here is the engine's
 * own relaxed state — drag nodes and the wires respond as matter.
 */
import { boot } from './shared'
import { mkMultiportStart, installDrag } from './multiport'

boot(
  'Wire physics — the engine IS the model',
  'plan 21: wires want to be short and straight, push nodes and are pushed; junctions settle at 120°; ∃ dots ride their wires; drag anything',
  (lab) => {
    installDrag(lab)
    lab.toast('drag any node — wires bend around discs, junctions re-balance, dangles follow')
  },
  mkMultiportStart,
)
