/**
 * ROUND 3 · A — contextual rule menu. Select something, then a STILL
 * right-click opens the menu of moves the kernel would entertain HERE
 * (discovery = the app's applicableActions; polarity-gated). Parameterized
 * moves show dimmed with a pointer to their round. 'Iterate into…' enters
 * the shared target phase. Kernel refusals land in the toast verbatim.
 */
import { boot, installBrush } from './shared'
import { commit, discover, installTargetPhase, installUndoKey, proveShowcase } from './prove'

boot('Round 3 · A — contextual rule menu', 'select, then STILL right-click = the moves legal here; Esc closes; Ctrl+Z undoes', (lab) => {
  let rightDown: { sx: number; sy: number } | null = null
  const brush = installBrush(lab, (_h, e) => {
    if (e.button !== 2) return false
    rightDown = { sx: e.clientX, sy: e.clientY }
    return true
  })
  installUndoKey(lab, brush)
  const picker = installTargetPhase(lab, brush)
  lab.canvas.addEventListener('contextmenu', (e) => e.preventDefault())

  let menu: HTMLDivElement | null = null
  const close = () => { menu?.remove(); menu = null }
  window.addEventListener('keydown', (e) => { if (e.key === 'Escape') close() })
  lab.canvas.addEventListener('pointerdown', () => close())

  lab.canvas.addEventListener('pointerup', (e) => {
    if (rightDown === null) return
    const rd = rightDown
    rightDown = null
    if (Math.hypot(e.clientX - rd.sx, e.clientY - rd.sy) > 4 || picker.active()) return
    close()
    const disc = discover(lab, brush.selected)
    if (disc === null) {
      lab.toast(brush.selected.length === 0 ? 'select something first — the menu lists ITS moves' : 'this selection spans several regions; pick within one region')
      return
    }
    menu = document.createElement('div')
    menu.style.cssText = `position:fixed;left:${Math.min(rd.sx, innerWidth - 260)}px;top:${Math.min(rd.sy, innerHeight - 300)}px;z-index:8;width:240px;background:#fff;border:1.5px solid #d97706;border-radius:8px;box-shadow:0 4px 16px #0003;font:13px system-ui;overflow:hidden`
    for (const a of disc.actions) {
      const parameterized = a.kind === 'insert' || a.kind === 'convert' || a.kind === 'instantiate' || a.kind === 'relFold' || a.kind === 'citeTheorem'
      const row = document.createElement('div')
      row.style.cssText = `padding:6px 10px;${parameterized ? 'color:#aaa' : 'cursor:pointer'}`
      row.textContent = parameterized ? `${a.label}  (round 4)` : a.label
      if (!parameterized) {
        row.addEventListener('pointerenter', () => { row.style.background = '#fde68a55' })
        row.addEventListener('pointerleave', () => { row.style.background = '' })
        row.addEventListener('click', () => {
          close()
          if (a.kind === 'iterate') picker.begin(disc.sel, a)
          else commit(lab, brush, disc.sel, a)
        })
      }
      menu.append(row)
    }
    document.body.append(menu)
  })
}, proveShowcase)
