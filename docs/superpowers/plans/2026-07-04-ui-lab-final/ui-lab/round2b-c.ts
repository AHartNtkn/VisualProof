/**
 * ROUND 2b · C — contextual cascade. A STILL right-click (the slash gesture
 * always moves, so the two coexist; selection is untouched) opens a compact
 * menu at the point: search row, λ-term entry, recents, then namespaces that
 * cascade into a scrollable submenu on hover. Every spawn lands exactly at
 * the clicked point — inside a cut included, which the old double-click
 * trigger structurally could not do (region discs eat every click).
 */
import { boot, promptAt, spawnRelAt, spawnTermAt, tryEdit, type LabCtx } from './shared'
import { installComposite } from './composite'
import { libId, mkRecents, searchLibrary, syntheticLibrary, type LibEntry } from './library'
import type { Vec2 } from '../src/view/vec'

const LIB = syntheticLibrary()
const recents = mkRecents(5)

boot('Round 2b · C — contextual cascade', 'STILL right-click opens the spawn menu at the point (drag still slashes); namespaces cascade; search on top', (lab) => {
  let menu: HTMLDivElement | null = null
  const close = () => { menu?.remove(); menu = null }
  installComposite(lab, { onRightStill: ({ sx, sy, world }) => openMenu(lab, sx, sy, world) })
  lab.canvas.addEventListener('pointerdown', () => close())
  window.addEventListener('keydown', (e) => { if (e.key === 'Escape') close() })

  function openMenu(lab2: LabCtx, sx: number, sy: number, world: Vec2): void {
    close()
    const region = lab2.regionAt(world)
    menu = document.createElement('div')
    menu.style.cssText = `position:fixed;left:${Math.min(sx, innerWidth - 380)}px;top:${Math.min(sy, innerHeight - 340)}px;z-index:8;display:flex;align-items:flex-start;font:13px system-ui`
    const col = document.createElement('div')
    col.style.cssText = 'width:180px;background:#fff;border:1.5px solid #d97706;border-radius:8px;box-shadow:0 4px 16px #0003;overflow:hidden'
    const sub = document.createElement('div')
    sub.style.cssText = 'width:170px;margin-left:2px;background:#fff;border:1px solid #ccc;border-radius:8px;box-shadow:0 4px 16px #0002;max-height:300px;overflow-y:auto;display:none'
    menu.append(col, sub)

    const spawn = (e: LibEntry): void => {
      if (tryEdit(lab2, () => {
        spawnRelAt(lab2, region, libId(e), e.arity, world)
        recents.note(e)
        lab2.toast(`${libId(e)}/${e.arity} placed in '${region}'`)
      })) close()
    }
    const item = (label: string, hint: string, onPick: (() => void) | null): HTMLDivElement => {
      const r = document.createElement('div')
      r.style.cssText = `display:flex;justify-content:space-between;gap:6px;padding:5px 10px;${onPick ? 'cursor:pointer' : 'color:#999'}`
      r.innerHTML = `<span>${label}</span><span style="color:#999">${hint}</span>`
      if (onPick) {
        r.addEventListener('pointerenter', () => { r.style.background = '#fde68a55' })
        r.addEventListener('pointerleave', () => { r.style.background = '' })
        r.addEventListener('click', onPick)
      }
      return r
    }

    const search = document.createElement('input')
    search.placeholder = `search… → '${region}'`
    search.style.cssText = 'width:100%;box-sizing:border-box;padding:6px 10px;border:none;border-bottom:1px solid #eee;outline:none;font:13px system-ui'
    const listing = document.createElement('div')
    listing.style.cssText = 'max-height:270px;overflow-y:auto'
    col.append(search, listing)

    const showNs = (ns: string, anchor: HTMLElement): void => {
      sub.replaceChildren(...LIB.filter((e) => e.ns === ns).map((e) => item(e.name, `/${e.arity}`, () => spawn(e))))
      sub.style.display = 'block'
      sub.style.marginTop = `${Math.max(0, anchor.offsetTop - 40)}px`
    }
    const tree = (): HTMLElement[] => {
      const out: HTMLElement[] = []
      out.push(item('λ term…', '', () => {
        close()
        promptAt(sx, sy, 'λ-term, e.g. \\x. x x', (t) =>
          tryEdit(lab2, () => { spawnTermAt(lab2, region, t, world); lab2.toast(`term added in '${region}'`) }))
      }))
      for (const e of recents.list()) out.push(item(e.name, `${e.ns}/${e.arity}`, () => spawn(e)))
      const seen = new Set<string>()
      for (const e of LIB) {
        if (seen.has(e.ns)) continue
        seen.add(e.ns)
        const count = LIB.filter((x) => x.ns === e.ns).length
        const r = item(e.ns, `${count} ▸`, null)
        r.style.cursor = 'pointer'
        r.style.color = ''
        r.addEventListener('pointerenter', () => { r.style.background = '#fde68a55'; showNs(e.ns, r) })
        r.addEventListener('pointerleave', () => { r.style.background = '' })
        out.push(r)
      }
      return out
    }
    const rebuild = () => {
      const q = search.value.trim()
      if (q === '') { listing.replaceChildren(...tree()); return }
      sub.style.display = 'none'
      const found = searchLibrary(LIB, q)
      const rows = found.slice(0, 14).map((e) => item(libId(e), `/${e.arity}`, () => spawn(e)))
      if (found.length > 14) rows.push(item(`…and ${found.length - 14} more`, '', null))
      if (found.length === 0) rows.push(item('no relation matches', '', null))
      listing.replaceChildren(...rows)
    }
    search.addEventListener('input', rebuild)
    search.addEventListener('keydown', (e) => {
      e.stopPropagation()
      if (e.key === 'Enter') { const first = searchLibrary(LIB, search.value)[0]; if (first) spawn(first) }
      else if (e.key === 'Escape') close()
    })
    rebuild()
    document.body.append(menu)
    setTimeout(() => search.focus(), 0)
  }
})
