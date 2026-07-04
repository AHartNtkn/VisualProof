/**
 * ROUND 6 · B — studio. Persistent chrome: a top toolbar (mode identity +
 * the lifecycle as buttons), a left LIBRARY panel (relations drag out in
 * EDIT; theorems listed with live applicability in PROVE — click to cite),
 * and the track timeline always docked. The bet: visibility of state and
 * vocabulary beats a clean sheet.
 */
import { boot, emptyStart, spawnRelAt, tryEdit } from './shared'
import { installGhostDrag } from './composite'
import { mkChromeApp } from './chrome'
import { citeCandidates } from './prove4'
import { applyStep } from '../src/kernel/proof/step'
import { occurrenceSelection } from '../src/kernel/diagram/subgraph/match'
import { mkSelection } from '../src/kernel/diagram/subgraph/selection'

boot('Round 6 · B — studio', 'toolbar + library panel + docked timeline; relations drag out in EDIT; theorems click-to-cite in PROVE', (lab) => {
  const app = mkChromeApp(lab)

  // ---- toolbar ----
  const bar = document.createElement('div')
  bar.style.cssText = 'position:fixed;left:0;right:0;top:32px;z-index:7;display:flex;gap:6px;align-items:center;padding:5px 10px;background:#f5f5f4;border-bottom:1px solid #ccc;font:13px system-ui'
  document.body.append(bar)
  const btn = (label: string, onClick: () => void): HTMLButtonElement => {
    const b = document.createElement('button')
    b.textContent = label
    b.style.cssText = 'font:13px system-ui;padding:3px 10px;border:1px solid #bbb;border-radius:6px;background:#fff;cursor:pointer'
    b.addEventListener('click', onClick)
    bar.append(b)
    return b
  }
  const modeBadge = document.createElement('span')
  modeBadge.style.cssText = 'font:600 13px system-ui;padding:3px 12px;border-radius:999px;color:#fff'
  bar.append(modeBadge)
  const guard = (fn: () => void) => { try { fn() } catch (e) { app.refuse(e instanceof Error ? e.message : String(e)) } }
  const bF = btn('prove forward (F)', () => guard(() => app.startTrack('forward')))
  const bB = btn('prove backward (B)', () => guard(() => app.startTrack('backward')))
  const bD = btn('declare… (D)', () => app.promptDeclare())
  const bE = btn('exit proof (E)', () => app.endTrack())

  // ---- library panel ----
  const panel = document.createElement('div')
  panel.style.cssText = 'position:fixed;left:0;top:66px;bottom:70px;width:220px;z-index:7;background:#fffffff2;border-right:1px solid #ccc;font:13px system-ui;overflow-y:auto;padding:6px'
  document.body.append(panel)
  const section = (title: string): HTMLDivElement => {
    const h = document.createElement('div')
    h.textContent = title
    h.style.cssText = 'padding:4px 6px;color:#999;font-size:11px;text-transform:uppercase'
    panel.append(h)
    return h
  }
  const rebuildPanel = () => {
    panel.replaceChildren()
    section('relations' + (app.mode() === 'edit' ? ' — drag onto the sheet' : ''))
    for (const [name, body] of app.ctx.relations) {
      const r = document.createElement('div')
      r.textContent = `${name}/${body.boundary.length}`
      r.style.cssText = `padding:4px 8px;border-radius:6px;user-select:none;${app.mode() === 'edit' ? 'cursor:grab' : 'color:#999'}`
      if (app.mode() === 'edit') {
        installGhostDrag(lab, r, name, (region, at) => {
          tryEdit(lab, () => { spawnRelAt(lab, region, name, body.boundary.length, at); lab.toast(`${name} placed in '${region}'`) })
        })
      }
      panel.append(r)
    }
    section(app.mode() === 'edit' ? 'theorems' : 'theorems — click to cite where applicable')
    if (app.mode() === 'edit') {
      for (const [name] of app.ctx.theorems) {
        const r = document.createElement('div')
        r.textContent = name
        r.style.cssText = 'padding:4px 8px;color:#555'
        panel.append(r)
      }
    } else {
      const direction = app.mode() === 'forward' ? 'forward' as const : 'reverse' as const
      const cands = citeCandidates(lab, app.ctx, [], direction)
      for (const c of [...cands.applicable, ...cands.closed]) {
        const r = document.createElement('div')
        const n = c.occs === null ? 'closed — inserts' : c.occs.length === 1 ? 'applies' : `${c.occs.length} places`
        r.innerHTML = `<span>${c.name}</span> <span style="color:#16a34a">${n}</span>`
        r.style.cssText = 'padding:4px 8px;border-radius:6px;cursor:pointer'
        r.addEventListener('pointerenter', () => { r.style.background = '#fde68a55' })
        r.addEventListener('pointerleave', () => { r.style.background = '' })
        r.addEventListener('click', () => guard(() => {
          const track = app.track()!
          const sink = track.sink(app.refuse)
          if (c.occs === null) {
            sink.apply({ rule: 'theorem', name: c.name, at: { sel: mkSelection(lab.d, { region: lab.d.root, regions: [], nodes: [], wires: [] }), args: [] }, direction: c.direction })
          } else {
            const occ = c.occs[0]!
            sink.apply({ rule: 'theorem', name: c.name, at: { sel: occurrenceSelection(c.from, occ, lab.d), args: [...occ.attachments] }, direction: c.direction })
            if (c.occs.length > 1) lab.toast(`cited at the first of ${c.occs.length} places — right-click to cycle instead`)
          }
        }))
        panel.append(r)
      }
    }
  }

  // ---- docked timeline ----
  const strip = document.createElement('div')
  strip.style.cssText = 'position:fixed;left:220px;right:0;bottom:28px;z-index:7;display:flex;align-items:center;gap:4px;padding:6px;background:#ffffffe8;border-top:1px solid #ccc;font:12px system-ui;flex-wrap:wrap;min-height:20px'
  document.body.append(strip)
  const chip = (label: string, strong: boolean, onClick?: () => void): HTMLElement => {
    const c = document.createElement('button')
    c.textContent = label
    c.style.cssText = `font:12px system-ui;padding:3px 9px;border-radius:999px;cursor:${onClick ? 'pointer' : 'default'};border:1.5px solid ${strong ? '#d97706' : '#bbb'};background:#fff`
    if (onClick) c.addEventListener('click', onClick)
    return c
  }
  const MODE = { edit: ['#b45309', 'EDIT'], forward: ['#15803d', 'FORWARD'], backward: ['#6d28d9', 'BACKWARD'] } as const
  const rebuild = () => {
    const m = app.mode()
    modeBadge.textContent = MODE[m][1]
    modeBadge.style.background = MODE[m][0]
    bF.disabled = bB.disabled = m !== 'edit'
    bD.disabled = bE.disabled = m === 'edit'
    for (const b of [bF, bB, bD, bE]) b.style.opacity = b.disabled ? '0.4' : '1'
    rebuildPanel()
    strip.replaceChildren()
    const track = app.track()
    if (track === null) { strip.append(chip('no proof running — the timeline docks here', false)); return }
    const jump = (k: number) => guard(() => track.rewind(k))
    strip.append(chip('origin', true, () => jump(0)))
    track.labels().forEach((l, i) => strip.append(chip(l, false, () => jump(i + 1))))
    strip.append(chip('● here', true))
  }
  app.onChange(rebuild)
  rebuild()
}, emptyStart)
