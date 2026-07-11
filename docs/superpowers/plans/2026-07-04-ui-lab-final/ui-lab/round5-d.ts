/**
 * ROUND 5 · D — derive, then DECLARE (the user's workflow ruling). No goal
 * ritual: the sheet is the starting point. Press F to prove FORWARD from
 * here or B to prove BACKWARD from here; apply moves; press D at any moment
 * to declare — the theorem is (origin ⟹ here) or (here ⟹ origin), the other
 * end falling out of the proof for free, kernel-checked by replay and
 * adopted (declare repeatedly: lemmas stack). The single-ended timeline
 * peeks past states. The two-ended meet (rounds 5a–c) remains the special
 * case for statements fixed a priori.
 */
import { boot, promptAt, type BrushHandle } from './shared'
import { renderPreview } from './prove'
import { installVerdictMoves, mkRefusalBubble } from './verdict'
import { mkTrackLab, sessionStart } from './session5'
import type { Diagram } from '../src/kernel/diagram/diagram'

boot('Round 5 · D — derive, then declare', 'F = prove forward from here · B = prove backward · D = declare (the other end falls out of the proof)', (lab) => {
  const track = mkTrackLab(lab)
  let brushRef: BrushHandle | null = null
  const refuse = mkRefusalBubble(lab, () => brushRef)
  const brush = installVerdictMoves(lab, track.sink(refuse))
  brushRef = brush

  const banner = document.createElement('div')
  banner.style.cssText = 'position:fixed;left:50%;transform:translateX(-50%);top:44px;z-index:7;padding:5px 16px;border-radius:0 0 10px 10px;font:600 13px system-ui;background:#78716c;color:#fff'
  document.body.append(banner)

  const strip = document.createElement('div')
  strip.style.cssText = 'position:fixed;left:0;right:0;bottom:28px;z-index:7;display:flex;justify-content:center;align-items:center;gap:4px;padding:6px;background:#ffffffe8;border-top:1px solid #ccc;font:12px system-ui;flex-wrap:wrap'
  document.body.append(strip)
  const peek = document.createElement('div')
  peek.style.cssText = 'position:fixed;right:8px;bottom:70px;z-index:8;display:none;background:#fff;border:1.5px solid #57534e;border-radius:8px;box-shadow:0 4px 16px #0003;font:12px system-ui'
  const peekLabel = document.createElement('div')
  peekLabel.style.cssText = 'padding:3px 8px;color:#57534e;border-bottom:1px solid #eee'
  const peekCanvas = document.createElement('canvas')
  peekCanvas.width = 300; peekCanvas.height = 210
  peek.append(peekLabel, peekCanvas)
  document.body.append(peek)
  window.addEventListener('keydown', (e) => { if (e.key === 'Escape') peek.style.display = 'none' })
  const showPeek = (label: string, d: Diagram): void => {
    peekLabel.textContent = label
    renderPreview(peekCanvas, d, track.boundary().filter((w) => d.wires[w] !== undefined))
    peek.style.display = 'block'
  }

  const chip = (label: string, opts: { strong?: boolean; onClick?: () => void; onHover?: () => void }): HTMLElement => {
    const c = document.createElement('button')
    c.textContent = label
    c.style.cssText = `font:12px system-ui;padding:3px 9px;border-radius:999px;cursor:${opts.onClick ? 'pointer' : 'default'};border:1.5px solid ${opts.strong ? '#d97706' : '#bbb'};background:#fff;${opts.strong ? 'font-weight:600;' : ''}`
    if (opts.onClick) c.addEventListener('click', opts.onClick)
    if (opts.onHover) c.addEventListener('pointerenter', opts.onHover)
    return c
  }
  const rebuild = () => {
    const dir = track.direction()
    banner.textContent = dir === null
      ? 'the sheet is the starting point — F: prove forward from here · B: prove backward from here'
      : `proving ${dir} — ${track.labels().length} step(s) · D declares ${dir === 'forward' ? '(origin ⟹ here)' : '(here ⟹ origin)'}`
    strip.replaceChildren()
    if (dir === null) return
    const states = track.states()
    // hover a chip to PEEK that state; CLICK to REWIND the track to it
    // (the user ruling: one click beats Ctrl+Z over and over)
    const jump = (k: number) => {
      try { track.rewind(k); peek.style.display = 'none'; lab.toast(k === 0 ? 'rewound to the origin' : `rewound to state ${k}`) }
      catch (err) { refuse(err instanceof Error ? err.message : String(err)) }
    }
    strip.append(chip('origin', { strong: true, onHover: () => showPeek('origin (click to rewind)', states[0]!), onClick: () => jump(0) }))
    track.labels().forEach((l, i) => strip.append(chip(l, {
      onHover: () => showPeek(`after step ${i + 1}: ${l} (click to rewind)`, states[i + 1]!),
      onClick: () => jump(i + 1),
    })))
    strip.append(chip('● here', { strong: true }))
    strip.append(chip('declare…', {
      strong: true,
      onClick: () => {
        promptAt(innerWidth / 2 - 100, 60, 'name the theorem', (name) => {
          if (name.trim() === '') { refuse('a theorem needs a name'); return false }
          try {
            track.declare(name.trim())
            lab.toast(`theorem '${name.trim()}' declared: ${track.direction() === 'forward' ? 'origin ⟹ here' : 'here ⟹ origin'} — checked by replay, added to the context`)
            return true
          } catch (e) { refuse(e instanceof Error ? e.message : String(e)); return false }
        })
      },
    }))
  }
  track.onChange(rebuild)
  rebuild()

  window.addEventListener('keydown', (e) => {
    if (document.activeElement instanceof HTMLInputElement) return
    const guard = (fn: () => void) => { try { fn() } catch (err) { refuse(err instanceof Error ? err.message : String(err)) } }
    if (e.key === 'f' || e.key === 'F') guard(() => { track.start('forward'); lab.toast('proving forward — every move is recorded; D declares') })
    else if (e.key === 'b' || e.key === 'B') guard(() => { track.start('backward'); lab.toast('proving backward — right-click for un-citations; D declares (here ⟹ origin)') })
    else if (e.key === 'd' || e.key === 'D') {
      if (track.direction() === null) { refuse('start proving first (F or B)'); return }
      promptAt(innerWidth / 2 - 100, 60, 'name the theorem', (name) => {
        if (name.trim() === '') { refuse('a theorem needs a name'); return false }
        try {
          track.declare(name.trim())
          lab.toast(`theorem '${name.trim()}' declared — checked by replay, added to the context`)
          return true
        } catch (err) { refuse(err instanceof Error ? err.message : String(err)); return false }
      })
    }
  })
}, sessionStart)
