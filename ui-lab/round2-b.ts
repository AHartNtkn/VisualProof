/**
 * ROUND 2 · B — "direct gestures". No verb bar: the sheet itself is the tool.
 *  - JOIN: drag from anywhere on a line onto another line (rubber band +
 *    green target highlight); a still click on a line just selects it.
 *  - SEVER: right-button drag draws a red slash; every strand it crosses is
 *    severed where crossed.
 *  - DRAW-A-CUT: drag on empty space sketches a lasso; release wraps what it
 *    encloses in a fresh cut (a tiny lasso is just an empty click).
 *  - CREATE: double-click empty space → inline λ-term input at that spot;
 *    relations drag out of the left palette.
 *  - Ctrl+Z undo, Delete removes the selection.
 */
import { boot, hitShapes, installBrush, installEditKeys, mergeWires, pointInPolygon, promptAt, severLeg, spawnRelAt, spawnTermAt, tryEdit, wrapHits, REL_PALETTE } from './shared'
import type { Hit } from '../src/app/hittest'
import type { Vec2 } from '../src/view/vec'

boot('Round 2 · B — direct gestures', 'drag line→line joins; right-drag slash severs; lasso empty space = cut; dbl-click = term; palette drags relations', (lab) => {
  let joinDrag: { wid: string; from: Vec2; cursor: Vec2; target: string | null; moved: boolean } | null = null
  let lasso: Vec2[] | null = null
  let slash: { a: Vec2; b: Vec2 } | null = null

  const brush = installBrush(lab, (h, e) => {
    if (e.button === 2) {
      const w = lab.toWorld(e.clientX, e.clientY)
      slash = { a: w, b: w }
      return true
    }
    if (h?.kind === 'wire') {
      const w = lab.toWorld(e.clientX, e.clientY)
      joinDrag = { wid: h.id, from: w, cursor: w, target: null, moved: false }
      return true
    }
    if (h === null) {
      lasso = [lab.toWorld(e.clientX, e.clientY)]
      return true
    }
    return false
  })
  installEditKeys(lab, brush)
  lab.canvas.addEventListener('contextmenu', (e) => e.preventDefault())

  lab.canvas.addEventListener('pointermove', (e) => {
    const w = lab.toWorld(e.clientX, e.clientY)
    if (slash) { slash.b = w; return }
    if (lasso) { lasso.push(w); return }
    if (joinDrag) {
      joinDrag.cursor = w
      if (Math.hypot(w.x - joinDrag.from.x, w.y - joinDrag.from.y) > 1.2) joinDrag.moved = true
      const h = lab.hitAt(e.clientX, e.clientY)
      joinDrag.target = h?.kind === 'wire' && h.id !== joinDrag.wid ? h.id : null
    }
  })
  lab.canvas.addEventListener('pointerup', () => {
    if (slash) {
      const cut = lab.legsCrossing(slash.a, slash.b)
      slash = null
      if (cut.length === 0) { lab.toast('the slash crossed no strand'); return }
      let n = 0
      for (const g of cut) if (severLeg(lab, g)) n++
      if (n > 0) { brush.prune(); lab.toast(`severed ${n} strand${n === 1 ? '' : 's'}`) }
      return
    }
    if (lasso) {
      const poly = lasso
      lasso = null
      const span = poly.reduce((s, p) => Math.max(s, Math.hypot(p.x - poly[0]!.x, p.y - poly[0]!.y)), 0)
      if (poly.length < 8 || span < 4) { brush.clear(); return } // just an empty click
      // parent = deepest region containing the whole stroke; children = its
      // direct nodes and child regions the lasso encloses
      let parent = lab.d.root
      let bestR = Infinity
      for (const [rid, g] of lab.engine.regions) {
        if (lab.d.regions[rid]!.kind === 'sheet') continue
        if (poly.every((p) => Math.hypot(p.x - g.center.x, p.y - g.center.y) <= g.radius) && g.radius < bestR) {
          parent = rid; bestR = g.radius
        }
      }
      const hits: Hit[] = []
      for (const [id, n] of Object.entries(lab.d.nodes)) {
        const b = lab.engine.bodies.get(id)
        if (n.region === parent && b && pointInPolygon(b.pos, poly)) hits.push({ kind: 'node', id })
      }
      for (const [id, r] of Object.entries(lab.d.regions)) {
        const g = lab.engine.regions.get(id)
        if (r.kind !== 'sheet' && r.parent === parent && g && pointInPolygon(g.center, poly)) hits.push({ kind: 'region', id })
      }
      if (hits.length === 0) { lab.toast('the lasso enclosed nothing'); return }
      if (tryEdit(lab, () => { wrapHits(lab, hits, null) })) { brush.prune(); lab.toast('cut drawn around the enclosed items') }
      return
    }
    if (joinDrag) {
      const jd = joinDrag
      joinDrag = null
      if (!jd.moved) {
        // a still click on a line = toggle-select it (brush semantics)
        const h: Hit = { kind: 'wire', id: jd.wid }
        const i = brush.selected.findIndex((s) => s.kind === 'wire' && s.id === jd.wid)
        if (i >= 0) brush.selected.splice(i, 1); else brush.selected.push(h)
        return
      }
      if (jd.target === null) { lab.toast('release on another line to join') ; return }
      tryEdit(lab, () => {
        lab.mutate(mergeWires(lab.d, jd.wid, jd.target!))
        brush.prune()
        lab.toast('lines joined — one individual now')
      })
    }
  })

  lab.canvas.addEventListener('dblclick', (e) => {
    const h = lab.hitAt(e.clientX, e.clientY)
    if (h !== null) return
    const w = lab.toWorld(e.clientX, e.clientY)
    const region = lab.regionAt(w)
    promptAt(e.clientX, e.clientY, 'λ-term, e.g. \\x. x x', (t) =>
      tryEdit(lab, () => {
        spawnTermAt(lab, region, t, w)
        lab.toast(`term added in '${region}'`)
      }))
  })

  // relation palette: pointer-drag a chip onto the sheet
  const palette = document.createElement('div')
  palette.style.cssText = 'position:fixed;left:8px;top:80px;z-index:7;display:flex;flex-direction:column;gap:6px;font:13px system-ui'
  document.body.append(palette)
  let ghost: { name: string; arity: number; el: HTMLDivElement } | null = null
  for (const r of REL_PALETTE) {
    const chip = document.createElement('div')
    chip.textContent = `${r.name}/${r.arity}`
    chip.style.cssText = 'padding:5px 10px;background:#fff;border:1px solid #bbb;border-radius:7px;cursor:grab;box-shadow:0 1px 4px #0002;user-select:none'
    chip.addEventListener('pointerdown', (e) => {
      const el = chip.cloneNode(true) as HTMLDivElement
      el.style.position = 'fixed'; el.style.zIndex = '9'; el.style.opacity = '0.85'; el.style.pointerEvents = 'none'
      el.style.left = `${e.clientX + 6}px`; el.style.top = `${e.clientY + 6}px`
      document.body.append(el)
      ghost = { name: r.name, arity: r.arity, el }
      e.preventDefault()
    })
    palette.append(chip)
  }
  window.addEventListener('pointermove', (e) => {
    if (ghost) { ghost.el.style.left = `${e.clientX + 6}px`; ghost.el.style.top = `${e.clientY + 6}px` }
  })
  window.addEventListener('pointerup', (e) => {
    if (ghost === null) return
    const g = ghost
    ghost = null
    g.el.remove()
    if (e.target !== lab.canvas) { lab.toast('drop the relation on the sheet'); return }
    const w = lab.toWorld(e.clientX, e.clientY)
    tryEdit(lab, () => {
      spawnRelAt(lab, lab.regionAt(w), g.name, g.arity, w)
      lab.toast(`${g.name}/${g.arity} placed`)
    })
  })

  lab.overlay((out) => {
    if (joinDrag && joinDrag.moved) {
      out.push({ kind: 'segment', from: joinDrag.from, to: joinDrag.cursor, stroke: '#16a34a', width: 1.6, glow: null })
      if (joinDrag.target !== null) out.push(...hitShapes(lab, { kind: 'wire', id: joinDrag.target }, '#16a34a', 3.2))
    }
    if (lasso && lasso.length > 1) {
      for (let i = 0; i + 1 < lasso.length; i++) {
        out.push({ kind: 'segment', from: lasso[i]!, to: lasso[i + 1]!, stroke: '#57534e', width: 1.2, glow: null })
      }
      out.push({ kind: 'segment', from: lasso[lasso.length - 1]!, to: lasso[0]!, stroke: '#57534e', width: 0.8, glow: null })
    }
    if (slash) out.push({ kind: 'segment', from: slash.a, to: slash.b, stroke: '#dc2626', width: 2, glow: null })
  })
})
