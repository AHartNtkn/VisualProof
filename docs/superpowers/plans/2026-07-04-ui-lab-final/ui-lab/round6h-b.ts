/**
 * ROUND 6h · B — LEDGER history. The derivation reads like a proof script:
 * a right-hand column, one row per step (origin at top, ● here at the
 * bottom), hover shows the state as a floating thumbnail, click rewinds.
 * Scales by scrolling; folds away to a tab. On the winning minimal chrome.
 */
import { boot, emptyStart } from './shared'
import { mkChromeApp, installMinimalChrome } from './chrome'
import { stateThumb } from './history'

boot('Round 6h · B — ledger', 'history as a proof script: a step column, hover thumbnails, click to rewind', (lab) => {
  const app = mkChromeApp(lab)
  installMinimalChrome(lab, app)

  const col = document.createElement('div')
  col.style.cssText = 'position:fixed;right:0;top:76px;bottom:34px;width:190px;z-index:7;display:none;flex-direction:column;background:#ffffffee;border-left:1px solid #ccc;font:12px system-ui'
  document.body.append(col)
  const head = document.createElement('div')
  head.style.cssText = 'padding:5px 10px;color:#999;font-size:11px;text-transform:uppercase;border-bottom:1px solid #eee;display:flex;justify-content:space-between'
  const rows = document.createElement('div')
  rows.style.cssText = 'flex:1;overflow-y:auto;padding:4px'
  const foot = document.createElement('div')
  foot.style.cssText = 'padding:6px;display:flex;gap:4px;border-top:1px solid #eee'
  col.append(head, rows, foot)

  const hoverThumb = document.createElement('div')
  hoverThumb.style.cssText = 'position:fixed;z-index:9;display:none;background:#fff;border:1.5px solid #57534e;border-radius:8px;box-shadow:0 4px 16px #0003;padding:4px'
  document.body.append(hoverThumb)

  const rebuild = () => {
    const track = app.track()
    if (track === null || track.direction() === null) { col.style.display = 'none'; hoverThumb.style.display = 'none'; return }
    col.style.display = 'flex'
    head.replaceChildren()
    head.append(`derivation · ${track.labels().length} step(s)`)
    rows.replaceChildren()
    const states = track.states()
    const labels = track.labels()
    const bd = track.boundary()
    const jump = (k: number) => { try { track.rewind(k) } catch (e) { app.refuse(e instanceof Error ? e.message : String(e)) } }
    states.forEach((d, k) => {
      const last = k === states.length - 1
      const r = document.createElement('div')
      r.textContent = k === 0 ? '0 · origin' : `${k} · ${labels[k - 1]}${last ? '  ●' : ''}`
      r.style.cssText = `padding:4px 8px;border-radius:6px;${last ? 'font-weight:600;color:#92400e' : 'cursor:pointer'}`
      if (!last) {
        r.addEventListener('pointerenter', (e) => {
          r.style.background = '#fde68a55'
          hoverThumb.replaceChildren(stateThumb(d, bd, 220, 154))
          hoverThumb.style.display = 'block'
          hoverThumb.style.right = '196px'
          hoverThumb.style.top = `${Math.min(e.clientY - 60, innerHeight - 200)}px`
        })
        r.addEventListener('pointerleave', () => { r.style.background = ''; hoverThumb.style.display = 'none' })
        r.addEventListener('click', () => { hoverThumb.style.display = 'none'; jump(k) })
      }
      rows.append(r)
    })
    rows.scrollTop = rows.scrollHeight
    foot.replaceChildren()
    const b = (label: string, onClick: () => void): HTMLButtonElement => {
      const x = document.createElement('button')
      x.textContent = label
      x.style.cssText = 'flex:1;font:12px system-ui;padding:3px 6px;border:1.5px solid #d97706;border-radius:999px;background:#fff;cursor:pointer'
      x.addEventListener('click', onClick)
      return x
    }
    foot.append(b('declare…', () => app.promptDeclare()), b('exit', () => app.endTrack()))
  }
  app.onChange(rebuild)
  rebuild()
}, emptyStart)
