/**
 * ROUND 2 · C — "stub-pull + radial". The Peirce-flavored set:
 *  - JOIN: grab a line's LOOSE END (the ∃ dot) and pull it; nearby lines
 *    magnetize (green); release to fuse. Mid-line drags still brush-select.
 *  - SEVER: double-click the strand you want detached.
 *  - CREATE + CUT: double-click empty space opens a radial menu at the spot —
 *    λ-term, empty cut, or one of the known relations, all landing there.
 *  - Lasso-wrap intentionally absent: this variant bets on "make an empty cut,
 *    then move things in" (A2 drag) versus B's draw-around.
 *  - Ctrl+Z undo, Delete removes the selection.
 */
import { boot, emptyCutAt, hitShapes, installBrush, installEditKeys, mergeWires, promptAt, severLeg, spawnRelAt, spawnTermAt, tryEdit, REL_PALETTE } from './shared'
import type { Vec2 } from '../src/view/vec'

boot('Round 2 · C — stub-pull + radial', 'pull a loose end onto another line to join; dbl-click a strand severs; dbl-click empty = radial create', (lab) => {
  let pull: { wid: string; from: Vec2; cursor: Vec2; target: string | null } | null = null

  const brush = installBrush(lab, (_h, e) => {
    const w = lab.toWorld(e.clientX, e.clientY)
    for (const s of lab.stubs()) {
      if (Math.hypot(w.x - s.dot.x, w.y - s.dot.y) < 3) {
        pull = { wid: s.wid, from: s.from, cursor: w, target: null }
        return true
      }
    }
    return false
  })
  installEditKeys(lab, brush)

  const SNAP = 6
  lab.canvas.addEventListener('pointermove', (e) => {
    if (pull === null) return
    pull.cursor = lab.toWorld(e.clientX, e.clientY)
    const wid = lab.wireNear(pull.cursor, SNAP)
    pull.target = wid !== null && wid !== pull.wid ? wid : null
  })
  lab.canvas.addEventListener('pointerup', () => {
    if (pull === null) return
    const p = pull
    pull = null
    if (p.target === null) { lab.toast('release near another line to fuse the loose end') ; return }
    tryEdit(lab, () => {
      lab.mutate(mergeWires(lab.d, p.wid, p.target!))
      brush.prune()
      lab.toast('loose end fused — one individual now')
    })
  })

  let radial: HTMLDivElement | null = null
  const closeRadial = () => { radial?.remove(); radial = null }
  window.addEventListener('keydown', (e) => { if (e.key === 'Escape') closeRadial() })
  lab.canvas.addEventListener('pointerdown', () => closeRadial())

  lab.canvas.addEventListener('dblclick', (e) => {
    const w = lab.toWorld(e.clientX, e.clientY)
    const g = lab.legAt(w, 2.5)
    if (g !== null) {
      if (severLeg(lab, g)) { brush.prune(); lab.toast('strand severed') }
      return
    }
    if (lab.hitAt(e.clientX, e.clientY) !== null) return
    closeRadial()
    const region = lab.regionAt(w)
    radial = document.createElement('div')
    radial.style.cssText = `position:fixed;left:${e.clientX}px;top:${e.clientY}px;z-index:8;width:0;height:0`
    const items: { label: string; act: () => void }[] = [
      {
        label: 'λ term…',
        act: () => promptAt(e.clientX - 90, e.clientY - 14, 'λ-term, e.g. \\x. x x', (t) =>
          tryEdit(lab, () => { spawnTermAt(lab, region, t, w); lab.toast(`term added in '${region}'`) })),
      },
      { label: '◯ cut', act: () => { tryEdit(lab, () => { emptyCutAt(lab, region, w); lab.toast(`empty cut drawn in '${region}'`) }) } },
      ...REL_PALETTE.map((r) => ({
        label: `${r.name}/${r.arity}`,
        act: () => { tryEdit(lab, () => { spawnRelAt(lab, region, r.name, r.arity, w); lab.toast(`${r.name}/${r.arity} placed`) }) },
      })),
    ]
    const R = 64
    items.forEach((it, i) => {
      const a = (i / items.length) * 2 * Math.PI - Math.PI / 2
      const b = document.createElement('button')
      b.textContent = it.label
      b.style.cssText = `position:absolute;left:${Math.cos(a) * R}px;top:${Math.sin(a) * R}px;transform:translate(-50%,-50%);font:12px system-ui;padding:4px 9px;border:1px solid #d97706;border-radius:999px;background:#fff;cursor:pointer;white-space:nowrap;box-shadow:0 1px 5px #0003`
      b.addEventListener('pointerdown', (ev) => ev.stopPropagation())
      b.addEventListener('click', () => { closeRadial(); it.act() })
      radial!.append(b)
    })
    document.body.append(radial)
  })

  lab.overlay((out) => {
    // make loose ends visibly grabbable: a faint halo on each ∃ dot
    for (const s of lab.stubs()) {
      out.push({ kind: 'circle', center: s.dot, r: 2.6, fill: '#16a34a22', stroke: '#16a34a', width: 0.7, insetColor: null, glow: null })
    }
    if (pull !== null) {
      out.push({ kind: 'segment', from: pull.from, to: pull.cursor, stroke: '#16a34a', width: 1.6, glow: null })
      if (pull.target !== null) out.push(...hitShapes(lab, { kind: 'wire', id: pull.target }, '#16a34a', 3.2))
    }
  })
})
