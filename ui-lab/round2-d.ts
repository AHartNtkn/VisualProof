/**
 * ROUND 2 · D — the composite of the Round-2 verdicts:
 *  - JOIN: drag line→line (B), plus J joins ALL selected lines at once.
 *  - SEVER: right-drag slash by default; an options toggle (⚙, top right)
 *    switches to double-click-a-strand. Both immediate.
 *  - WRAP: Space = cut around the selection, Shift+Space = SO bubble.
 *    Selecting a cut AND things inside it wraps the subtree once (absorbed).
 *  - MOVE: dragging a SELECTED node moves it; dropping it inside another
 *    region moves it THERE (wires it owns travel along) — "make an empty cut,
 *    then move things in" now works.
 *  - DELETE: works across regions; deleting a cut dissolves its boundary and
 *    the unselected contents propagate up.
 *  - SPAWN (interim, pending the spawn-browser design round): drag chips from
 *    the left palette; the λ-term chip opens an inline input where dropped.
 */
import { absorbHits, boot, hitShapes, installBrush, installEditKeys, mergeAllWires, promptAt, reparentNode, severLeg, spawnRelAt, spawnTermAt, tryEdit, wrapHits, REL_PALETTE } from './shared'
import type { Hit } from '../src/app/hittest'
import type { Vec2 } from '../src/view/vec'

boot('Round 2 · D — composite', 'drag joins · slash (or dbl-click, see ⚙) severs · Space cuts around · Shift+Space bubbles · drag selected node moves it · Delete dissolves', (lab) => {
  let severMode: 'slash' | 'dblclick' = 'slash'
  let joinDrag: { wid: string; from: Vec2; cursor: Vec2; target: string | null; moved: boolean } | null = null
  let slash: { a: Vec2; b: Vec2 } | null = null
  let moveDrag: { nid: string; cursor: Vec2; moved: boolean } | null = null

  const brush = installBrush(lab, (h, e) => {
    if (e.button === 2) {
      if (severMode !== 'slash') { lab.toast('sever is set to double-click (change it under ⚙)'); return true }
      const w = lab.toWorld(e.clientX, e.clientY)
      slash = { a: w, b: w }
      return true
    }
    if (h?.kind === 'node' && brush.isSelected(h)) {
      moveDrag = { nid: h.id, cursor: lab.toWorld(e.clientX, e.clientY), moved: false }
      lab.freeze(true)
      return true
    }
    if (h?.kind === 'wire') {
      const w = lab.toWorld(e.clientX, e.clientY)
      joinDrag = { wid: h.id, from: w, cursor: w, target: null, moved: false }
      return true
    }
    return false
  })
  installEditKeys(lab, brush)
  lab.canvas.addEventListener('contextmenu', (e) => e.preventDefault())

  lab.canvas.addEventListener('pointermove', (e) => {
    const w = lab.toWorld(e.clientX, e.clientY)
    if (slash) { slash.b = w; return }
    if (moveDrag) {
      if (Math.hypot(w.x - moveDrag.cursor.x, w.y - moveDrag.cursor.y) > 0.8) moveDrag.moved = true
      moveDrag.cursor = w
      return
    }
    if (joinDrag) {
      joinDrag.cursor = w
      if (Math.hypot(w.x - joinDrag.from.x, w.y - joinDrag.from.y) > 1.2) joinDrag.moved = true
      const wid = lab.wireNear(w, 4)
      joinDrag.target = wid !== null && wid !== joinDrag.wid ? wid : null
    }
  })
  lab.onFrame(() => {
    if (moveDrag === null) return
    const b = lab.engine.bodies.get(moveDrag.nid)
    if (b) { b.pos.x = moveDrag.cursor.x; b.pos.y = moveDrag.cursor.y }
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
    if (moveDrag) {
      const md = moveDrag
      moveDrag = null
      lab.freeze(false)
      if (!md.moved) {
        // a still click on a selected node = brush toggle-off
        const i = brush.selected.findIndex((s) => s.kind === 'node' && s.id === md.nid)
        if (i >= 0) brush.selected.splice(i, 1)
        return
      }
      const dest = lab.regionAt(md.cursor)
      const home = lab.d.nodes[md.nid]!.region
      if (dest === home) return
      tryEdit(lab, () => {
        lab.mutate(reparentNode(lab.d, md.nid, dest), { node: md.nid, at: md.cursor })
        lab.toast(`moved into '${dest}'`)
      })
      return
    }
    if (joinDrag) {
      const jd = joinDrag
      joinDrag = null
      if (!jd.moved) {
        const h: Hit = { kind: 'wire', id: jd.wid }
        const i = brush.selected.findIndex((s) => s.kind === 'wire' && s.id === jd.wid)
        if (i >= 0) brush.selected.splice(i, 1); else brush.selected.push(h)
        return
      }
      if (jd.target === null) { lab.toast('release on another line to join'); return }
      tryEdit(lab, () => {
        lab.mutate(mergeAllWires(lab.d, [jd.wid, jd.target!]))
        brush.prune()
        lab.toast('lines joined — one individual now')
      })
    }
  })

  lab.canvas.addEventListener('dblclick', (e) => {
    if (severMode !== 'dblclick') return
    const g = lab.legAt(lab.toWorld(e.clientX, e.clientY), 2.5)
    if (g !== null && severLeg(lab, g)) { brush.prune(); lab.toast('strand severed') }
  })

  window.addEventListener('keydown', (e) => {
    if (document.activeElement instanceof HTMLInputElement) return
    if (e.key === ' ') {
      e.preventDefault()
      if (brush.selected.length === 0) { lab.toast('select what the cut should go around first'); return }
      if (e.shiftKey) {
        promptAt(innerWidth / 2 - 100, 60, 'bubble arity (e.g. 1)', (t) => {
          const n = Number(t)
          if (!Number.isInteger(n) || n < 0) { lab.toast(`'${t}' is not a valid arity`); return false }
          if (tryEdit(lab, () => { wrapHits(lab, absorbHits(lab.d, brush.selected), n) })) {
            brush.clear(); lab.toast('wrapped in a bubble'); return true
          }
          return false
        })
      } else if (tryEdit(lab, () => { wrapHits(lab, absorbHits(lab.d, brush.selected), null) })) {
        brush.clear(); lab.toast('cut drawn around the selection')
      }
    } else if (e.key === 'j' || e.key === 'J') {
      const wids = brush.selected.filter((h) => h.kind === 'wire').map((h) => h.id)
      tryEdit(lab, () => {
        lab.mutate(mergeAllWires(lab.d, wids))
        brush.prune()
        lab.toast(`joined ${wids.length} lines — one individual now`)
      })
    }
  })

  // options (⚙): sever gesture toggle — slash default, dbl-click alternative
  const opts = document.createElement('div')
  opts.style.cssText = 'position:fixed;right:8px;top:40px;z-index:7;font:13px system-ui;background:#ffffffe8;border:1px solid #ccc;border-radius:8px;padding:6px 8px;box-shadow:0 1px 5px #0002'
  const sevBtn = document.createElement('button')
  sevBtn.style.cssText = 'font:13px system-ui;padding:2px 8px;border:1px solid #bbb;border-radius:6px;background:#fff;cursor:pointer'
  const syncOpts = () => { sevBtn.textContent = severMode === 'slash' ? 'right-drag slash' : 'double-click strand' }
  syncOpts()
  sevBtn.addEventListener('click', () => { severMode = severMode === 'slash' ? 'dblclick' : 'slash'; syncOpts() })
  opts.append('⚙ sever: ', sevBtn)
  document.body.append(opts)

  // interim spawn palette (the real spawn browser is its own design round)
  const palette = document.createElement('div')
  palette.style.cssText = 'position:fixed;left:8px;top:80px;z-index:7;display:flex;flex-direction:column;gap:6px;font:13px system-ui'
  document.body.append(palette)
  let ghost: { spawn: (region: string, at: Vec2, sx: number, sy: number) => void; el: HTMLDivElement } | null = null
  const chip = (label: string, spawn: (region: string, at: Vec2, sx: number, sy: number) => void): void => {
    const c = document.createElement('div')
    c.textContent = label
    c.style.cssText = 'padding:5px 10px;background:#fff;border:1px solid #bbb;border-radius:7px;cursor:grab;box-shadow:0 1px 4px #0002;user-select:none'
    c.addEventListener('pointerdown', (e) => {
      const el = c.cloneNode(true) as HTMLDivElement
      el.style.position = 'fixed'; el.style.zIndex = '9'; el.style.opacity = '0.85'; el.style.pointerEvents = 'none'
      el.style.left = `${e.clientX + 6}px`; el.style.top = `${e.clientY + 6}px`
      document.body.append(el)
      ghost = { spawn, el }
      e.preventDefault()
    })
    palette.append(c)
  }
  chip('λ term…', (region, at, sx, sy) => {
    promptAt(sx, sy, 'λ-term, e.g. \\x. x x', (t) =>
      tryEdit(lab, () => { spawnTermAt(lab, region, t, at); lab.toast(`term added in '${region}'`) }))
  })
  for (const r of REL_PALETTE) {
    chip(`${r.name}/${r.arity}`, (region, at) => {
      tryEdit(lab, () => { spawnRelAt(lab, region, r.name, r.arity, at); lab.toast(`${r.name}/${r.arity} placed in '${region}'`) })
    })
  }
  window.addEventListener('pointermove', (e) => {
    if (ghost) { ghost.el.style.left = `${e.clientX + 6}px`; ghost.el.style.top = `${e.clientY + 6}px` }
  })
  window.addEventListener('pointerup', (e) => {
    if (ghost === null) return
    const g = ghost
    ghost = null
    g.el.remove()
    if (e.target !== lab.canvas) { lab.toast('drop it on the sheet'); return }
    const w = lab.toWorld(e.clientX, e.clientY)
    g.spawn(lab.regionAt(w), w, e.clientX, e.clientY)
  })

  lab.overlay((out) => {
    if (joinDrag && joinDrag.moved) {
      out.push({ kind: 'segment', from: joinDrag.from, to: joinDrag.cursor, stroke: '#16a34a', width: 1.6, glow: null })
      if (joinDrag.target !== null) out.push(...hitShapes(lab, { kind: 'wire', id: joinDrag.target }, '#16a34a', 3.2))
    }
    if (slash) out.push({ kind: 'segment', from: slash.a, to: slash.b, stroke: '#dc2626', width: 2, glow: null })
    if (moveDrag && moveDrag.moved) {
      const dest = lab.regionAt(moveDrag.cursor)
      const g = lab.engine.regions.get(dest)
      if (g && lab.d.regions[dest]!.kind !== 'sheet' && dest !== lab.d.nodes[moveDrag.nid]!.region) {
        out.push({ kind: 'circle', center: g.center, r: g.radius, fill: '#16a34a10', stroke: '#16a34a', width: 1.6, insetColor: null, glow: null })
      }
    }
  })
})
