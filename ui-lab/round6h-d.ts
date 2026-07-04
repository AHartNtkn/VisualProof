/**
 * ROUND 6h · D — the verdict composite. The scrubber IS undo/redo (C's
 * ruling): dragging the thin bottom bar moves the REAL cursor — the future
 * is retained and redo reaches it; a new move from an earlier point discards
 * it. Ctrl+Z / Ctrl+Shift+Z step the cursor. Hovering a tick pops a
 * thumbnail ZOOMED to what that step changed (A's readability verdict) —
 * whole-diagram miniatures blur together; the change doesn't.
 */
import { boot, emptyStart } from './shared'
import { mkChromeApp, installMinimalChrome } from './chrome'
import { zoomThumb, stateThumb } from './history'

boot('Round 6h · D — scrubber = undo/redo', 'drag the bar: real time travel, future retained; new moves discard it; hover a tick = the change, zoomed; Ctrl+Z / Ctrl+Shift+Z', (lab) => {
  const app = mkChromeApp(lab)
  installMinimalChrome(lab, app)

  const bar = document.createElement('div')
  bar.style.cssText = 'position:fixed;left:10%;right:18%;bottom:40px;height:26px;z-index:7;display:none;align-items:center;cursor:ew-resize'
  const rail = document.createElement('div')
  rail.style.cssText = 'position:absolute;left:0;right:0;height:4px;top:11px;background:#d6d3d1;border-radius:2px'
  bar.append(rail)
  document.body.append(bar)
  const caption = document.createElement('div')
  caption.style.cssText = 'position:fixed;left:50%;transform:translateX(-50%);bottom:14px;z-index:7;display:none;color:#666;font:12px system-ui'
  document.body.append(caption)
  const chips = document.createElement('div')
  chips.style.cssText = 'position:fixed;right:8px;bottom:36px;z-index:7;display:none;gap:4px'
  const chip = (label: string, onClick: () => void): HTMLButtonElement => {
    const c = document.createElement('button')
    c.textContent = label
    c.style.cssText = 'font:12px system-ui;padding:3px 10px;border:1.5px solid #d97706;border-radius:999px;background:#fff;cursor:pointer;margin-left:4px'
    c.addEventListener('click', onClick)
    chips.append(c)
    return c
  }
  chip('declare…', () => app.promptDeclare())
  chip('exit (E)', () => app.endTrack())
  document.body.append(chips)
  const pop = document.createElement('div')
  pop.style.cssText = 'position:fixed;z-index:9;display:none;background:#fff;border:1.5px solid #57534e;border-radius:8px;box-shadow:0 4px 16px #0003;padding:4px;font:11px system-ui;text-align:center;color:#57534e'
  document.body.append(pop)

  let dragging = false
  const layout = () => {
    const track = app.track()
    bar.querySelectorAll('.tick').forEach((t) => t.remove())
    if (track === null || track.direction() === null) {
      bar.style.display = 'none'; caption.style.display = 'none'; chips.style.display = 'none'; pop.style.display = 'none'
      return
    }
    bar.style.display = 'flex'
    chips.style.display = 'flex'
    const states = track.states()
    const labels = track.labels()
    const bd = track.boundary()
    const n = states.length
    const cur = track.cursor()
    for (let k = 0; k < n; k++) {
      const t = document.createElement('div')
      t.className = 'tick'
      const frac = n === 1 ? 1 : k / (n - 1)
      const isCur = k === cur
      const future = k > cur
      t.style.cssText = `position:absolute;top:${isCur ? 4 : 7}px;width:${isCur ? 12 : 8}px;height:${isCur ? 18 : 12}px;border-radius:4px;transform:translateX(-50%);left:${frac * 100}%;background:${isCur ? '#d97706' : future ? '#d6d3d1' : '#a8a29e'};${future ? 'border:1px dashed #a8a29e;' : ''}`
      t.addEventListener('pointerenter', (e) => {
        if (dragging) return
        pop.replaceChildren(
          k === 0 ? stateThumb(states[0]!, bd, 220, 154) : zoomThumb(states[k - 1]!, states[k]!, bd),
          Object.assign(document.createElement('div'), { textContent: k === 0 ? 'origin' : `${labels[k - 1]}${future ? ' (future — redo reaches it)' : ''}` }),
        )
        pop.style.display = 'block'
        pop.style.left = `${Math.min(Math.max(8, e.clientX - 110), innerWidth - 240)}px`
        pop.style.bottom = '74px'
      })
      t.addEventListener('pointerleave', () => { pop.style.display = 'none' })
      bar.append(t)
    }
    caption.style.display = 'block'
    caption.textContent = cur === 0 ? `origin${n > 1 ? ' — redo (Ctrl+Shift+Z) walks forward' : ''}` : `${cur}/${n - 1} · ${labels[cur - 1]}${cur < n - 1 ? ' — future retained' : ''}`
  }
  const kAt = (clientX: number): number => {
    const r = bar.getBoundingClientRect()
    const n = app.track()!.states().length
    return Math.max(0, Math.min(n - 1, Math.round(((clientX - r.left) / r.width) * (n - 1))))
  }
  bar.addEventListener('pointerdown', (e) => {
    const track = app.track()
    if (track === null) return
    dragging = true
    pop.style.display = 'none'
    const k = kAt(e.clientX)
    if (k !== track.cursor()) track.rewind(k)
    e.preventDefault()
  })
  window.addEventListener('pointermove', (e) => {
    if (!dragging) return
    const track = app.track()!
    const k = kAt(e.clientX)
    if (k !== track.cursor()) track.rewind(k)
  })
  window.addEventListener('pointerup', () => { dragging = false })
  app.onChange(layout)
  layout()
}, emptyStart)
