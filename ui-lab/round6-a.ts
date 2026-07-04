/**
 * ROUND 6 · A — minimal sheet. The diagram IS the app: no panels, no
 * toolbars. A mode pill (color = mode) floats top-center; the track timeline
 * appears only while proving; the memory box only once there is history;
 * everything else is contextual (right-click = spawn cascade in EDIT, move
 * menu in PROVE; all the decided keys). '?' shows the keyboard map.
 */
import { boot, emptyStart } from './shared'
import { renderPreview } from './prove'
import { mkChromeApp } from './chrome'
import type { Diagram } from '../src/kernel/diagram/diagram'

boot('Round 6 · A — minimal sheet', 'right-click spawns (EDIT) / lists moves (PROVE) · F/B start a proof from the sheet · D declares · E exits · ? = keys', (lab) => {
  const app = mkChromeApp(lab)

  // mode pill: the one permanent piece of chrome
  const pill = document.createElement('div')
  pill.style.cssText = 'position:fixed;left:50%;transform:translateX(-50%);top:44px;z-index:7;padding:5px 18px;border-radius:0 0 12px 12px;font:600 13px system-ui;color:#fff'
  document.body.append(pill)

  // track timeline (only while proving): hover peeks, click rewinds
  const strip = document.createElement('div')
  strip.style.cssText = 'position:fixed;left:0;right:0;bottom:28px;z-index:7;display:none;justify-content:center;align-items:center;gap:4px;padding:6px;background:#ffffffe8;border-top:1px solid #ccc;font:12px system-ui;flex-wrap:wrap'
  document.body.append(strip)
  const peek = document.createElement('div')
  peek.style.cssText = 'position:fixed;right:8px;bottom:70px;z-index:8;display:none;background:#fff;border:1.5px solid #57534e;border-radius:8px;box-shadow:0 4px 16px #0003;font:12px system-ui'
  const peekLabel = document.createElement('div')
  peekLabel.style.cssText = 'padding:3px 8px;color:#57534e;border-bottom:1px solid #eee'
  const peekCanvas = document.createElement('canvas')
  peekCanvas.width = 300; peekCanvas.height = 210
  peek.append(peekLabel, peekCanvas)
  document.body.append(peek)
  const showPeek = (label: string, d: Diagram): void => {
    peekLabel.textContent = label
    renderPreview(peekCanvas, d, (app.track()?.boundary() ?? []).filter((w) => d.wires[w] !== undefined))
    peek.style.display = 'block'
  }
  window.addEventListener('keydown', (e) => { if (e.key === 'Escape') peek.style.display = 'none' })

  const chip = (label: string, strong: boolean, onClick?: () => void, onHover?: () => void): HTMLElement => {
    const c = document.createElement('button')
    c.textContent = label
    c.style.cssText = `font:12px system-ui;padding:3px 9px;border-radius:999px;cursor:${onClick ? 'pointer' : 'default'};border:1.5px solid ${strong ? '#d97706' : '#bbb'};background:#fff;${strong ? 'font-weight:600;' : ''}`
    if (onClick) c.addEventListener('click', onClick)
    if (onHover) c.addEventListener('pointerenter', onHover)
    return c
  }
  const MODE_STYLE = { edit: ['#b45309', 'EDIT — construct freely'], forward: ['#15803d', 'PROVING FORWARD — D declares (origin ⟹ here)'], backward: ['#6d28d9', 'PROVING BACKWARD — D declares (here ⟹ origin)'] } as const
  const rebuild = () => {
    const m = app.mode()
    pill.style.background = MODE_STYLE[m][0]
    pill.textContent = MODE_STYLE[m][1]
    const track = app.track()
    if (track === null || track.direction() === null) { strip.style.display = 'none'; return }
    strip.style.display = 'flex'
    strip.replaceChildren()
    const states = track.states()
    const jump = (k: number) => { try { track.rewind(k); peek.style.display = 'none' } catch (err) { app.refuse(err instanceof Error ? err.message : String(err)) } }
    strip.append(chip('origin', true, () => jump(0), () => showPeek('origin (click to rewind)', states[0]!)))
    track.labels().forEach((l, i) => strip.append(chip(l, false, () => jump(i + 1), () => showPeek(`after ${l} (click to rewind)`, states[i + 1]!))))
    strip.append(chip('● here', true))
    strip.append(chip('declare…', true, () => app.promptDeclare()))
    strip.append(chip('exit (E)', false, () => app.endTrack()))
  }
  app.onChange(rebuild)
  rebuild()

  // '?' keyboard map overlay
  const help = document.createElement('div')
  help.style.cssText = 'position:fixed;left:50%;top:50%;transform:translate(-50%,-50%);z-index:10;display:none;background:#fff;border:1.5px solid #d97706;border-radius:10px;box-shadow:0 8px 30px #0004;padding:14px 18px;font:13px/1.7 system-ui;white-space:pre'
  help.textContent = [
    'EDIT   right-click: spawn cascade · drag line→line: join · J: join selected',
    '       right-drag: slash sever (⚙ toggles dbl-click) · W/Shift+W: cut/bubble wrap',
    '       drag selected node: move between regions · Delete: dissolve/delete · Ctrl+Z',
    'PROVE  F/B: start forward/backward from the sheet · right-click: moves legal here',
    '       Delete: contextual deletion · W/Shift+W: wraps · drag selection: iterate',
    '       dbl-click term: normalize · Tab/Enter: cycle/apply citation · D: declare · E: exit',
    'ALWAYS Ctrl+drag: physics handle (no meaning) · ?: this map · Esc: close things',
  ].join('\n')
  document.body.append(help)
  window.addEventListener('keydown', (e) => {
    if (document.activeElement instanceof HTMLInputElement) return
    if (e.key === '?') help.style.display = help.style.display === 'none' ? 'block' : 'none'
    else if (e.key === 'Escape') help.style.display = 'none'
  })
}, emptyStart)
