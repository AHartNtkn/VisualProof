/**
 * VARIANT C — "Scope climber" (structure-aware). Clicking the SAME spot
 * repeatedly climbs the containment ladder: node → its enclosing region's
 * whole subtree → the parent region's subtree → … → back to the node.
 * Hover previews the level a click would take (whole-subtree glow, with
 * polarity named in the readout). One gesture, every granularity — built
 * for a deeply nested calculus.
 */
import { boot, hitShapes, sameHit, readout } from './shared'
import type { Hit } from '../src/app/hittest'
import type { RegionId } from '../src/kernel/diagram/diagram'

boot('Round 1 · C — scope climber', 'repeat-click climbs node → cut subtree → parent…; hover previews the level', (lab) => {
  let hover: Hit | null = null
  let ladder: Hit[] = []      // the climb ladder at the anchor spot
  let level = -1              // current rung
  let selected: Hit[] = []    // rendered selection (subtree-expanded)
  const ladderFor = (h: Hit): Hit[] => {
    const rungs: Hit[] = [h]
    let r: RegionId | null =
      h.kind === 'node' ? lab.d.nodes[h.id]!.region
      : h.kind === 'wire' ? lab.d.wires[h.id]!.scope
      : lab.d.regions[h.id]!.kind === 'sheet' ? null : (lab.d.regions[h.id] as { parent: RegionId }).parent
    if (h.kind === 'region') rungs.length = 0, rungs.push(h)
    while (r !== null && lab.d.regions[r]!.kind !== 'sheet') {
      rungs.push({ kind: 'region', id: r })
      const reg = lab.d.regions[r]!
      r = reg.kind === 'sheet' ? null : reg.parent
    }
    return rungs
  }
  const expand = (h: Hit): Hit[] => h.kind === 'region' ? lab.subtreeHits(h.id) : [h]
  lab.canvas.addEventListener('pointermove', (e) => {
    hover = lab.hitAt(e.clientX, e.clientY)
    if (hover === null) { readout(''); return }
    const preview = sameHit(hover, ladder[0] ?? null) && level >= 0 ? ladder[(level + 1) % ladder.length]! : hover
    readout(`next click: ${lab.describe(preview)}${preview.kind === 'region' ? ' — whole subtree' : ''}`)
  })
  lab.canvas.addEventListener('pointerdown', (e) => {
    const h = lab.hitAt(e.clientX, e.clientY)
    if (h === null) { selected = []; ladder = []; level = -1; return }
    if (ladder.length > 0 && sameHit(h, ladder[0]!)) {
      level = (level + 1) % ladder.length
    } else {
      ladder = ladderFor(h)
      level = 0
    }
    selected = expand(ladder[level]!)
  })
  lab.overlay((out) => {
    for (const s of selected) out.push(...hitShapes(lab, s, '#d97706', s.kind === 'region' ? 2.8 : 2.2))
    if (hover) {
      const preview = ladder.length > 0 && sameHit(hover, ladder[0]!) ? ladder[(level + 1) % ladder.length]! : hover
      for (const s of expand(preview)) out.push(...hitShapes(lab, s, '#2563eb', 1.4))
    }
  })
})
