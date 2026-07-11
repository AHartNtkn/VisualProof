/**
 * ROUND 2b · A — command palette. Press "/" and a search box opens AT THE
 * CURSOR; typing filters the whole library (~140 relations); ↑↓ + Enter (or
 * click) spawns the pick exactly where the palette was invoked — inside a cut
 * included, since the trigger is a key, not an empty-space click. A leading
 * "\" switches to λ-term entry. Empty query shows recents. Esc closes.
 */
import { boot, spawnRelAt, spawnTermAt, tryEdit, type LabCtx } from './shared'
import { installComposite } from './composite'
import { libId, mkRecents, searchLibrary, syntheticLibrary, type LibEntry } from './library'
import type { Vec2 } from '../src/view/vec'

const LIB = syntheticLibrary()
const recents = mkRecents(8)

boot('Round 2b · A — command palette', 'press "/" — search spawns at the cursor; "\\…" enters a λ-term; empty query = recents', (lab) => {
  installComposite(lab)
  let last = { sx: innerWidth / 2, sy: innerHeight / 2 }
  lab.canvas.addEventListener('pointermove', (e) => { last = { sx: e.clientX, sy: e.clientY } })

  let box: HTMLDivElement | null = null
  const close = () => { box?.remove(); box = null }
  window.addEventListener('keydown', (e) => {
    if (document.activeElement instanceof HTMLInputElement) return
    if (e.key === '/') { e.preventDefault(); openPalette(lab, last.sx, last.sy) }
    else if (e.key === 'Escape') close()
  })

  function openPalette(lab2: LabCtx, sx: number, sy: number): void {
    close()
    const at: Vec2 = lab2.toWorld(sx, sy)
    const region = lab2.regionAt(at)
    box = document.createElement('div')
    box.style.cssText = `position:fixed;left:${Math.min(sx, innerWidth - 300)}px;top:${Math.min(sy, innerHeight - 320)}px;z-index:8;width:280px;background:#fff;border:1.5px solid #d97706;border-radius:8px;box-shadow:0 4px 16px #0003;font:13px system-ui;overflow:hidden`
    const input = document.createElement('input')
    input.placeholder = `search relations… (\\ for λ-term) → '${region}'`
    input.style.cssText = 'width:100%;box-sizing:border-box;padding:7px 10px;border:none;border-bottom:1px solid #eee;outline:none;font:13px system-ui'
    const list = document.createElement('div')
    list.style.cssText = 'max-height:250px;overflow-y:auto'
    box.append(input, list)
    document.body.append(box)

    type Item = { label: string; hint: string; run: () => boolean }
    let items: Item[] = []
    let sel = 0
    const spawnItem = (e: LibEntry): Item => ({
      label: libId(e), hint: `/${e.arity}`,
      run: () => tryEdit(lab2, () => {
        spawnRelAt(lab2, region, libId(e), e.arity, at)
        recents.note(e)
        lab2.toast(`${libId(e)}/${e.arity} placed in '${region}'`)
      }),
    })
    const render = () => {
      list.replaceChildren(...items.map((it, i) => {
        const row = document.createElement('div')
        row.style.cssText = `display:flex;justify-content:space-between;padding:5px 10px;cursor:pointer;${i === sel ? 'background:#fde68a' : ''}`
        row.innerHTML = `<span>${it.label}</span><span style="color:#999">${it.hint}</span>`
        row.addEventListener('pointerdown', (ev) => ev.preventDefault())
        row.addEventListener('click', () => { if (it.run()) close() })
        return row
      }))
    }
    const compute = () => {
      const q = input.value
      sel = 0
      if (q.startsWith('\\')) {
        items = [{
          label: `λ  ${q}`, hint: 'Enter spawns the term',
          run: () => tryEdit(lab2, () => { spawnTermAt(lab2, region, q, at); lab2.toast(`term added in '${region}'`) }),
        }]
      } else if (q.trim() === '') {
        items = recents.list().map(spawnItem)
        if (items.length === 0) items = [{ label: 'type to search 140 relations…', hint: '', run: () => false }]
      } else {
        const found = searchLibrary(LIB, q)
        items = found.slice(0, 12).map(spawnItem)
        if (found.length > 12) items.push({ label: `…and ${found.length - 12} more — keep typing`, hint: '', run: () => false })
        if (found.length === 0) items = [{ label: 'no relation matches', hint: '', run: () => false }]
      }
      render()
    }
    input.addEventListener('input', compute)
    input.addEventListener('keydown', (e) => {
      e.stopPropagation()
      if (e.key === 'ArrowDown') { sel = Math.min(sel + 1, items.length - 1); render(); e.preventDefault() }
      else if (e.key === 'ArrowUp') { sel = Math.max(sel - 1, 0); render(); e.preventDefault() }
      else if (e.key === 'Enter') { const it = items[sel]; if (it && it.run()) close() }
      else if (e.key === 'Escape') close()
    })
    input.addEventListener('blur', () => setTimeout(close, 120))
    compute()
    setTimeout(() => input.focus(), 0)
  }
})
