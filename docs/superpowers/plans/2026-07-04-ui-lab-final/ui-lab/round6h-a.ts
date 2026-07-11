/**
 * ROUND 6h · A — FILMSTRIP history. The derivation is a row of PICTURES:
 * every state renders as a thumbnail (origin → each step → here), captioned
 * with the move that produced it. Click any frame to rewind there. The strip
 * scrolls horizontally for long proofs; the current frame is ringed. On the
 * winning minimal chrome.
 */
import { boot, emptyStart } from './shared'
import { mkChromeApp, installMinimalChrome } from './chrome'
import { stateThumb } from './history'

boot('Round 6h · A — filmstrip', 'history as pictures: thumbnails per state, captions per move, click to rewind', (lab) => {
  const app = mkChromeApp(lab)
  installMinimalChrome(lab, app)

  const strip = document.createElement('div')
  strip.style.cssText = 'position:fixed;left:0;right:0;bottom:28px;z-index:7;display:none;gap:8px;align-items:flex-end;padding:8px 12px;background:#ffffffee;border-top:1px solid #ccc;overflow-x:auto;font:11px system-ui'
  document.body.append(strip)

  const frame = (canvas: HTMLCanvasElement, caption: string, current: boolean, onClick?: () => void): HTMLElement => {
    const f = document.createElement('div')
    f.style.cssText = `flex:0 0 auto;display:flex;flex-direction:column;align-items:center;gap:2px;cursor:${onClick ? 'pointer' : 'default'}`
    canvas.style.border = current ? '2.5px solid #d97706' : '1px solid #ccc'
    canvas.style.borderRadius = '6px'
    canvas.style.background = '#faf9f5'
    f.append(canvas)
    const cap = document.createElement('div')
    cap.textContent = caption
    cap.style.cssText = `max-width:132px;text-align:center;color:${current ? '#92400e' : '#666'};${current ? 'font-weight:600;' : ''}`
    f.append(cap)
    if (onClick) f.addEventListener('click', onClick)
    return f
  }
  const rebuild = () => {
    const track = app.track()
    if (track === null || track.direction() === null) { strip.style.display = 'none'; return }
    strip.style.display = 'flex'
    strip.replaceChildren()
    const states = track.states()
    const labels = track.labels()
    const bd = track.boundary()
    const jump = (k: number) => { try { track.rewind(k) } catch (e) { app.refuse(e instanceof Error ? e.message : String(e)) } }
    states.forEach((d, k) => {
      const last = k === states.length - 1
      strip.append(frame(
        stateThumb(d, bd),
        k === 0 ? 'origin' : labels[k - 1]! + (last ? '  · here' : ''),
        last,
        last ? undefined : () => jump(k),
      ))
    })
    const tail = document.createElement('div')
    tail.style.cssText = 'flex:0 0 auto;display:flex;flex-direction:column;gap:4px;padding-bottom:14px'
    const b = (label: string, onClick: () => void): HTMLButtonElement => {
      const x = document.createElement('button')
      x.textContent = label
      x.style.cssText = 'font:12px system-ui;padding:3px 10px;border:1.5px solid #d97706;border-radius:999px;background:#fff;cursor:pointer'
      x.addEventListener('click', onClick)
      return x
    }
    tail.append(b('declare…', () => app.promptDeclare()), b('exit (E)', () => app.endTrack()))
    strip.append(tail)
    strip.scrollLeft = strip.scrollWidth
  }
  app.onChange(rebuild)
  rebuild()
}, emptyStart)
