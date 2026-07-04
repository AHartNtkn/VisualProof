/**
 * Round-6h shared bits: cached state thumbnails (a visual proof assistant's
 * history should be VISUAL) — one small render per state, cached by the
 * immutable diagram object.
 */
import type { Diagram, WireId } from '../src/kernel/diagram/diagram'
import type { LabCtx } from './shared'
import type { ChromeApp } from './chrome'
import { renderPreview } from './prove'

const cache = new WeakMap<Diagram, HTMLCanvasElement>()

export function stateThumb(d: Diagram, boundary: readonly WireId[], w = 132, h = 92): HTMLCanvasElement {
  const hit = cache.get(d)
  if (hit !== undefined) return hit
  const c = document.createElement('canvas')
  c.width = w * 2; c.height = h * 2 // crisp on hidpi
  c.style.width = `${w}px`; c.style.height = `${h}px`
  renderPreview(c, d, boundary.filter((x) => d.wires[x] !== undefined))
  cache.set(d, c)
  return c
}

/** The bodies a step touched: fresh nodes plus the wire bodies of fresh
    wires (engine convention j:/x:). Empty on pure removals — callers fall
    back to the whole diagram. */
export function changedBodies(before: Diagram, after: Diagram): string[] {
  const out: string[] = []
  for (const id of Object.keys(after.nodes)) if (before.nodes[id] === undefined) out.push(id)
  for (const id of Object.keys(after.wires)) {
    if (before.wires[id] === undefined) { out.push(`j:${id}`, `x:${id}`) }
  }
  return out
}

const zoomCache = new WeakMap<Diagram, Map<Diagram, HTMLCanvasElement>>()

/** A thumbnail of `after` ZOOMED to what the step changed (A's readability
    verdict: whole-diagram miniatures blur together; the change doesn't). */
export function zoomThumb(before: Diagram, after: Diagram, boundary: readonly WireId[], w = 220, h = 154): HTMLCanvasElement {
  let byAfter = zoomCache.get(before)
  if (byAfter?.has(after)) return byAfter.get(after)!
  const c = document.createElement('canvas')
  c.width = w * 2; c.height = h * 2
  c.style.width = `${w}px`; c.style.height = `${h}px`
  renderPreview(c, after, boundary.filter((x) => after.wires[x] !== undefined), changedBodies(before, after))
  if (byAfter === undefined) { byAfter = new Map(); zoomCache.set(before, byAfter) }
  byAfter.set(after, c)
  return c
}

/** The round-6h verdict history surface: the thin scrubber IS undo/redo —
    dragging moves the real cursor (future retained, dashed; a new move
    discards it); hovering anywhere on the bar pops the nearest state's
    change, ZOOMED. Factored so the round-7 winner stack composes it. */
export function installScrubber(lab: LabCtx, app: ChromeApp): void {
  const bar = document.createElement('div')
  bar.style.cssText = 'position:fixed;left:10%;right:18%;bottom:40px;height:26px;z-index:7;display:none;align-items:center;cursor:ew-resize'
  // ticks live on an INSET inner rail so the extreme ticks (0% / 100%) sit
  // strictly inside the bar's hover zone — the edge tick must still preview
  const inner = document.createElement('div')
  inner.style.cssText = 'position:absolute;left:12px;right:12px;top:0;bottom:0'
  const rail = document.createElement('div')
  rail.style.cssText = 'position:absolute;left:0;right:0;height:4px;top:11px;background:#d6d3d1;border-radius:2px'
  inner.append(rail)
  bar.append(inner)
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
    inner.querySelectorAll('.tick').forEach((t) => t.remove())
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
      t.style.pointerEvents = 'none' // the BAR drives hover — no dead zones
      inner.append(t)
    }
    caption.style.display = 'block'
    caption.textContent = cur === 0 ? `origin${n > 1 ? ' — redo (Ctrl+Shift+Z) walks forward' : ''}` : `${cur}/${n - 1} · ${labels[cur - 1]}${cur < n - 1 ? ' — future retained' : ''}`
  }
  const kAt = (clientX: number): number => {
    const r = inner.getBoundingClientRect()
    const n = app.track()!.states().length
    return Math.max(0, Math.min(n - 1, Math.round(((clientX - r.left) / r.width) * (n - 1))))
  }
  // hover ANYWHERE on the bar previews the nearest tick — wherever the
  // resize cursor shows, the preview comes (no feedback without payoff)
  bar.addEventListener('pointermove', (e) => {
    if (dragging) return
    const track = app.track()
    if (track === null || track.direction() === null) return
    const states = track.states()
    const labels = track.labels()
    const bd = track.boundary()
    const k = kAt(e.clientX)
    const future = k > track.cursor()
    pop.replaceChildren(
      k === 0 ? stateThumb(states[0]!, bd, 220, 154) : zoomThumb(states[k - 1]!, states[k]!, bd),
      Object.assign(document.createElement('div'), { textContent: k === 0 ? 'origin' : `${labels[k - 1]}${future ? ' (future — redo reaches it)' : ''}` }),
    )
    pop.style.display = 'block'
    pop.style.left = `${Math.min(Math.max(8, e.clientX - 110), innerWidth - 240)}px`
    pop.style.bottom = '74px'
  })
  bar.addEventListener('pointerleave', () => { if (!dragging) pop.style.display = 'none' })
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
}
