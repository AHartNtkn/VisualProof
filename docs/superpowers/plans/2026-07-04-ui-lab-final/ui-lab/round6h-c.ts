/**
 * ROUND 6h · C — TIME SCRUBBER. History is a timeline you DRAG: a slim bar
 * with one tick per state; scrubbing travels the MAIN VIEW through the past
 * (the diagram itself time-travels, not an inset). Release to dwell at a
 * state — Enter rewinds the proof there, Esc snaps back to now; all other
 * input is held while dwelling. On the winning minimal chrome.
 */
import { boot, emptyStart } from './shared'
import { mkChromeApp, installMinimalChrome } from './chrome'

boot('Round 6h · C — time scrubber', 'drag the bar: the MAIN VIEW time-travels; release to dwell, Enter rewinds there, Esc returns to now', (lab) => {
  const app = mkChromeApp(lab)
  installMinimalChrome(lab, app)

  const bar = document.createElement('div')
  bar.style.cssText = 'position:fixed;left:10%;right:10%;bottom:40px;height:26px;z-index:7;display:none;align-items:center;cursor:ew-resize'
  const rail = document.createElement('div')
  rail.style.cssText = 'position:absolute;left:0;right:0;height:4px;top:11px;background:#d6d3d1;border-radius:2px'
  bar.append(rail)
  document.body.append(bar)
  const dwellBanner = document.createElement('div')
  dwellBanner.style.cssText = 'position:fixed;left:50%;transform:translateX(-50%);bottom:74px;z-index:8;display:none;padding:5px 14px;border-radius:999px;background:#57534e;color:#fff;font:600 12px system-ui'
  document.body.append(dwellBanner)
  const caption = document.createElement('div')
  caption.style.cssText = 'position:fixed;left:50%;transform:translateX(-50%);bottom:14px;z-index:7;display:none;color:#666;font:12px system-ui'
  document.body.append(caption)

  let scrub: { k: number; dwelling: boolean } | null = null
  const ticks: HTMLElement[] = []
  const layout = () => {
    const track = app.track()
    bar.querySelectorAll('.tick').forEach((t) => t.remove())
    ticks.length = 0
    if (track === null || track.direction() === null) { bar.style.display = 'none'; caption.style.display = 'none'; return }
    bar.style.display = 'flex'
    const n = track.states().length
    for (let k = 0; k < n; k++) {
      const t = document.createElement('div')
      t.className = 'tick'
      const frac = n === 1 ? 1 : k / (n - 1)
      const cur = scrub === null ? k === n - 1 : k === scrub.k
      t.style.cssText = `position:absolute;top:${cur ? 4 : 7}px;width:${cur ? 12 : 8}px;height:${cur ? 18 : 12}px;border-radius:4px;transform:translateX(-50%);left:${frac * 100}%;background:${cur ? '#d97706' : '#a8a29e'}`
      bar.append(t)
      ticks.push(t)
    }
    const k = scrub?.k ?? n - 1
    caption.style.display = 'block'
    caption.textContent = k === 0 ? 'origin' : k === n - 1 && scrub === null ? `here — ${track.labels()[k - 1]}` : `after: ${track.labels()[k - 1]}`
  }

  const show = (k: number) => {
    const track = app.track()!
    const d = track.states()[k]!
    lab.mutate(d, undefined, track.boundary().filter((w) => d.wires[w] !== undefined))
  }
  const kAt = (clientX: number): number => {
    const r = bar.getBoundingClientRect()
    const n = app.track()!.states().length
    return Math.max(0, Math.min(n - 1, Math.round(((clientX - r.left) / r.width) * (n - 1))))
  }
  bar.addEventListener('pointerdown', (e) => {
    const track = app.track()
    if (track === null) return
    scrub = { k: kAt(e.clientX), dwelling: false }
    show(scrub.k)
    layout()
    e.preventDefault()
  })
  window.addEventListener('pointermove', (e) => {
    if (scrub === null || scrub.dwelling) return
    const k = kAt(e.clientX)
    if (k !== scrub.k) { scrub.k = k; show(k); layout() }
  })
  window.addEventListener('pointerup', () => {
    if (scrub === null || scrub.dwelling) return
    const track = app.track()!
    if (scrub.k === track.states().length - 1) { scrub = null; layout(); return } // released at now
    scrub.dwelling = true
    dwellBanner.style.display = 'block'
    dwellBanner.textContent = `viewing state ${scrub.k}/${track.states().length - 1} — Enter rewinds here · Esc returns to now`
  })
  // while dwelling, hold every other input: this is a LOOK, not a state
  const guard = (e: Event) => {
    if (scrub?.dwelling && !(e instanceof KeyboardEvent && (e.key === 'Enter' || e.key === 'Escape'))) {
      e.stopImmediatePropagation()
      e.preventDefault()
    }
  }
  lab.canvas.addEventListener('pointerdown', guard, { capture: true })
  window.addEventListener('keydown', (e) => {
    if (scrub === null || !scrub.dwelling) return
    if (e.key === 'Enter') {
      const k = scrub.k
      scrub = null
      dwellBanner.style.display = 'none'
      try { app.track()!.rewind(k); lab.toast(`rewound to state ${k}`) } catch (err) { app.refuse(err instanceof Error ? err.message : String(err)) }
      layout()
    } else if (e.key === 'Escape') {
      const track = app.track()!
      scrub = null
      dwellBanner.style.display = 'none'
      show(track.states().length - 1)
      layout()
    } else guard(e)
  }, { capture: true })
  app.onChange(layout)
  layout()
}, emptyStart)
