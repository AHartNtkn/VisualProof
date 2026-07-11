/**
 * ROUND 6 · C — summon. As minimal as 6a, but with ONE unified summonable
 * surface: '/' opens a command palette at the cursor that searches EVERYTHING
 * relevant to the current mode — actions (start/declare/exit/undo), spawns
 * (EDIT: relations + λ-term), citations (PROVE: theorems applicable HERE).
 * Every path has a keyboard route; the mouse never has to leave the work.
 */
import { boot, emptyStart, spawnRelAt, spawnTermAt, promptAt, tryEdit } from './shared'
import { mkChromeApp } from './chrome'
import { citeCandidates } from './prove4'
import { occurrenceSelection } from '../src/kernel/diagram/subgraph/match'
import { mkSelection } from '../src/kernel/diagram/subgraph/selection'

boot('Round 6 · C — summon', "'/' = the palette: actions + spawns (EDIT) + applicable citations (PROVE), searched together; F/B/D/E still direct", (lab) => {
  const app = mkChromeApp(lab)

  const hud = document.createElement('div')
  hud.style.cssText = 'position:fixed;right:8px;top:40px;z-index:7;padding:4px 12px;border-radius:999px;font:600 12px system-ui;color:#fff'
  document.body.append(hud)
  const MODE = { edit: ['#b45309', 'EDIT'], forward: ['#15803d', 'FORWARD'], backward: ['#6d28d9', 'BACKWARD'] } as const
  const syncHud = () => { hud.textContent = MODE[app.mode()][1] + ' · / summons'; hud.style.background = MODE[app.mode()][0] }
  app.onChange(syncHud)
  syncHud()

  let lastMouse = { sx: innerWidth / 2, sy: innerHeight / 2 }
  lab.canvas.addEventListener('pointermove', (e) => { lastMouse = { sx: e.clientX, sy: e.clientY } })
  let box: HTMLDivElement | null = null
  const close = () => { box?.remove(); box = null }
  const guard = (fn: () => void) => { try { fn() } catch (e) { app.refuse(e instanceof Error ? e.message : String(e)) } }

  type Item = { label: string; hint: string; run: () => void }
  const items = (): Item[] => {
    const out: Item[] = []
    const m = app.mode()
    if (m === 'edit') {
      out.push({ label: 'prove forward from here', hint: 'F', run: () => guard(() => app.startTrack('forward')) })
      out.push({ label: 'prove backward from here', hint: 'B', run: () => guard(() => app.startTrack('backward')) })
      out.push({
        label: 'spawn λ term…', hint: '', run: () => {
          const at = { ...lastMouse }
          const world = lab.toWorld(at.sx, at.sy)
          promptAt(at.sx, at.sy, 'λ-term, e.g. \\x. x x', (t) =>
            tryEdit(lab, () => { spawnTermAt(lab, lab.regionAt(world), t, world); lab.toast('term added') }))
        },
      })
      for (const [name, body] of app.ctx.relations) {
        out.push({
          label: `spawn ${name}`, hint: `/${body.boundary.length}`, run: () => {
            const world = lab.toWorld(lastMouse.sx, lastMouse.sy)
            guard(() => { spawnRelAt(lab, lab.regionAt(world), name, body.boundary.length, world); lab.toast(`${name} placed`) })
          },
        })
      }
      out.push({ label: 'undo', hint: 'Ctrl+Z', run: () => { if (!lab.undo()) lab.toast('nothing to undo') } })
    } else {
      out.push({ label: 'declare theorem…', hint: 'D', run: () => app.promptDeclare() })
      out.push({ label: 'exit proof (keep the sheet)', hint: 'E', run: () => app.endTrack() })
      const direction = m === 'forward' ? 'forward' as const : 'reverse' as const
      const cands = citeCandidates(lab, app.ctx, [], direction)
      const track = app.track()!
      const sink = track.sink(app.refuse)
      for (const c of cands.applicable) {
        out.push({
          label: `cite ${c.name}`, hint: c.occs!.length === 1 ? 'applies' : `${c.occs!.length} places`, run: () => guard(() => {
            const occ = c.occs![0]!
            sink.apply({ rule: 'theorem', name: c.name, at: { sel: occurrenceSelection(c.from, occ, lab.d), args: [...occ.attachments] }, direction: c.direction })
          }),
        })
      }
      for (const c of cands.closed) {
        out.push({
          label: `insert ${c.name}`, hint: 'closed', run: () => guard(() => {
            sink.apply({ rule: 'theorem', name: c.name, at: { sel: mkSelection(lab.d, { region: lab.d.root, regions: [], nodes: [], wires: [] }), args: [] }, direction: c.direction })
          }),
        })
      }
    }
    return out
  }

  const openPalette = (): void => {
    close()
    const at = { ...lastMouse }
    box = document.createElement('div')
    box.style.cssText = `position:fixed;left:${Math.min(at.sx, innerWidth - 300)}px;top:${Math.min(at.sy, innerHeight - 320)}px;z-index:9;width:280px;background:#fff;border:1.5px solid #d97706;border-radius:8px;box-shadow:0 4px 16px #0003;font:13px system-ui;overflow:hidden`
    const input = document.createElement('input')
    input.placeholder = `${app.mode()} — search actions…`
    input.style.cssText = 'width:100%;box-sizing:border-box;padding:7px 10px;border:none;border-bottom:1px solid #eee;outline:none;font:13px system-ui'
    const list = document.createElement('div')
    list.style.cssText = 'max-height:260px;overflow-y:auto'
    box.append(input, list)
    document.body.append(box)
    let sel = 0
    let shown: Item[] = []
    const render = () => {
      const q = input.value.trim().toLowerCase()
      shown = items().filter((it) => q === '' || it.label.toLowerCase().includes(q))
      sel = Math.min(sel, Math.max(0, shown.length - 1))
      list.replaceChildren(...shown.map((it, i) => {
        const r = document.createElement('div')
        r.style.cssText = `display:flex;justify-content:space-between;padding:5px 10px;cursor:pointer;${i === sel ? 'background:#fde68a' : ''}`
        r.innerHTML = `<span>${it.label}</span><span style="color:#999">${it.hint}</span>`
        r.addEventListener('pointerdown', (ev) => ev.preventDefault())
        r.addEventListener('click', () => { close(); it.run() })
        return r
      }))
    }
    input.addEventListener('input', render)
    input.addEventListener('keydown', (e) => {
      e.stopPropagation()
      if (e.key === 'ArrowDown') { sel = Math.min(sel + 1, shown.length - 1); render(); e.preventDefault() }
      else if (e.key === 'ArrowUp') { sel = Math.max(sel - 1, 0); render(); e.preventDefault() }
      else if (e.key === 'Enter') { const it = shown[sel]; if (it) { close(); it.run() } }
      else if (e.key === 'Escape') close()
    })
    input.addEventListener('blur', () => setTimeout(close, 120))
    render()
    setTimeout(() => input.focus(), 0)
  }
  window.addEventListener('keydown', (e) => {
    if (document.activeElement instanceof HTMLInputElement) return
    if (e.key === '/') { e.preventDefault(); openPalette() }
  })
}, emptyStart)
