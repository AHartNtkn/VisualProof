/**
 * The Round-2 composite construction environment, factored so spawn-surface
 * variants (Round 2b) share it verbatim: brush selection, drag-join + J,
 * slash/double-click sever behind the ⚙ toggle, W/Shift+W wrap (cut/bubble —
 * the round-3 ruling moved wraps off Space, which is freed),
 * selected-node move with region drop, dissolve-delete, undo.
 * A still right-click is surfaced via `onRightStill` (spawn-menu hook);
 * only a moved right-drag slashes.
 */
import { absorbHits, hitShapes, installBrush, installEditKeys, mergeAllWires, promptAt, reparentNode, severLeg, tryEdit, wrapHits, type BrushHandle, type LabCtx } from './shared'
import type { Hit } from '../src/app/hittest'
import type { Vec2 } from '../src/view/vec'

export type CompositeOpts = {
  /** A right-button press released without movement (the gesture slash never
      uses) — the spawn-menu trigger that coexists with selection. */
  onRightStill?: (at: { sx: number; sy: number; world: Vec2 }) => void
  /** Mode gate: construction listens only while this is true (chrome pages
      host EDIT and PROVE vocabularies on one canvas). Absent = always on. */
  active?: () => boolean
}

export function installComposite(lab: LabCtx, opts: CompositeOpts = {}): { brush: BrushHandle } {
  const act = opts.active ?? (() => true)
  let severMode: 'slash' | 'dblclick' = 'slash'
  let joinDrag: { wid: string; from: Vec2; cursor: Vec2; target: string | null; moved: boolean } | null = null
  let slash: { a: Vec2; b: Vec2; sx: number; sy: number } | null = null
  let moveDrag: { nid: string; cursor: Vec2; moved: boolean } | null = null

  const brush = installBrush(lab, (h, e) => {
    if (e.button === 2) {
      const w = lab.toWorld(e.clientX, e.clientY)
      slash = { a: w, b: w, sx: e.clientX, sy: e.clientY }
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
  }, act)
  installEditKeys(lab, brush, act)
  lab.canvas.addEventListener('contextmenu', (e) => e.preventDefault())

  lab.canvas.addEventListener('pointermove', (e) => {
    if (!act()) return
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
    if (!act()) { slash = null; moveDrag = null; joinDrag = null; return }
    if (slash) {
      const s = slash
      slash = null
      const moved = Math.hypot(s.b.x - s.a.x, s.b.y - s.a.y) > 1
      if (!moved) {
        if (opts.onRightStill) opts.onRightStill({ sx: s.sx, sy: s.sy, world: s.a })
        return
      }
      if (severMode !== 'slash') { lab.toast('sever is set to double-click (change it under ⚙)'); return }
      const cut = lab.legsCrossing(s.a, s.b)
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
    if (!act() || severMode !== 'dblclick') return
    const g = lab.legAt(lab.toWorld(e.clientX, e.clientY), 2.5)
    if (g !== null && severLeg(lab, g)) { brush.prune(); lab.toast('strand severed') }
  })

  window.addEventListener('keydown', (e) => {
    if (!act()) return
    if (document.activeElement instanceof HTMLInputElement) return
    if (e.key === 'w' || e.key === 'W') {
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
  const optsBox = document.createElement('div')
  optsBox.style.cssText = 'position:fixed;right:8px;top:40px;z-index:7;font:13px system-ui;background:#ffffffe8;border:1px solid #ccc;border-radius:8px;padding:6px 8px;box-shadow:0 1px 5px #0002'
  const sevBtn = document.createElement('button')
  sevBtn.style.cssText = 'font:13px system-ui;padding:2px 8px;border:1px solid #bbb;border-radius:6px;background:#fff;cursor:pointer'
  const syncOpts = () => { sevBtn.textContent = severMode === 'slash' ? 'right-drag slash' : 'double-click strand' }
  syncOpts()
  sevBtn.addEventListener('click', () => { severMode = severMode === 'slash' ? 'dblclick' : 'slash'; syncOpts() })
  optsBox.append('⚙ sever: ', sevBtn)
  document.body.append(optsBox)
  lab.onFrame(() => { optsBox.style.display = act() ? 'block' : 'none' })

  lab.overlay((out) => {
    if (!act()) return
    if (joinDrag && joinDrag.moved) {
      out.push({ kind: 'segment', from: joinDrag.from, to: joinDrag.cursor, stroke: '#16a34a', width: 1.6, glow: null })
      if (joinDrag.target !== null) out.push(...hitShapes(lab, { kind: 'wire', id: joinDrag.target }, '#16a34a', 3.2))
    }
    if (slash && severMode === 'slash') out.push({ kind: 'segment', from: slash.a, to: slash.b, stroke: '#dc2626', width: 2, glow: null })
    if (moveDrag && moveDrag.moved) {
      const dest = lab.regionAt(moveDrag.cursor)
      const g = lab.engine.regions.get(dest)
      if (g && lab.d.regions[dest]!.kind !== 'sheet' && dest !== lab.d.nodes[moveDrag.nid]!.region) {
        out.push({ kind: 'circle', center: g.center, r: g.radius, fill: '#16a34a10', stroke: '#16a34a', width: 1.6, insetColor: null, glow: null })
      }
    }
  })
  return { brush }
}

/** Pointer-based drag-out-of-chrome: press on `el`, a ghost follows the
    cursor, releasing over the canvas calls `drop` with the point. */
export function installGhostDrag(lab: LabCtx, el: HTMLElement, label: string, drop: (region: string, at: Vec2, sx: number, sy: number) => void): void {
  el.addEventListener('pointerdown', (e) => {
    const ghost = document.createElement('div')
    ghost.textContent = label
    ghost.style.cssText = 'position:fixed;z-index:9;opacity:0.85;pointer-events:none;padding:5px 10px;background:#fff;border:1px solid #bbb;border-radius:7px;font:13px system-ui;box-shadow:0 1px 4px #0002'
    ghost.style.left = `${e.clientX + 6}px`; ghost.style.top = `${e.clientY + 6}px`
    document.body.append(ghost)
    const move = (ev: PointerEvent) => { ghost.style.left = `${ev.clientX + 6}px`; ghost.style.top = `${ev.clientY + 6}px` }
    const up = (ev: PointerEvent) => {
      window.removeEventListener('pointermove', move)
      window.removeEventListener('pointerup', up)
      ghost.remove()
      if (ev.target !== lab.canvas) { lab.toast('drop it on the sheet'); return }
      const w = lab.toWorld(ev.clientX, ev.clientY)
      drop(lab.regionAt(w), w, ev.clientX, ev.clientY)
    }
    window.addEventListener('pointermove', move)
    window.addEventListener('pointerup', up)
    e.preventDefault()
  })
}
