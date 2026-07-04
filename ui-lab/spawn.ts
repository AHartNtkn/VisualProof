/**
 * The decided spawn surface (round 2b verdict: the contextual cascade),
 * factored for chrome pages and running against REAL relations: still
 * right-click in EDIT opens it at the point — search row, λ-term entry,
 * relation rows — and everything spawns exactly where clicked.
 */
import type { ProofContext } from '../src/kernel/proof/step'
import type { Vec2 } from '../src/view/vec'
import { promptAt, spawnRelAt, spawnTermAt, tryEdit, type LabCtx } from './shared'

let menu: HTMLDivElement | null = null
export function closeSpawnCascade(): void { menu?.remove(); menu = null }

export function openSpawnCascade(lab: LabCtx, ctx: ProofContext, at: { sx: number; sy: number }, world: Vec2): void {
  closeSpawnCascade()
  const region = lab.regionAt(world)
  menu = document.createElement('div')
  menu.style.cssText = `position:fixed;left:${Math.min(at.sx, innerWidth - 240)}px;top:${Math.min(at.sy, innerHeight - 300)}px;z-index:8;width:220px;background:#fff;border:1.5px solid #d97706;border-radius:8px;box-shadow:0 4px 16px #0003;font:13px system-ui;overflow:hidden`
  const search = document.createElement('input')
  search.placeholder = `spawn… → '${region}'`
  search.style.cssText = 'width:100%;box-sizing:border-box;padding:6px 10px;border:none;border-bottom:1px solid #eee;outline:none;font:13px system-ui'
  const listing = document.createElement('div')
  listing.style.cssText = 'max-height:250px;overflow-y:auto'
  menu.append(search, listing)
  const row = (label: string, hint: string, onPick: () => void): HTMLDivElement => {
    const r = document.createElement('div')
    r.style.cssText = 'display:flex;justify-content:space-between;gap:6px;padding:5px 10px;cursor:pointer'
    r.innerHTML = `<span>${label}</span><span style="color:#999">${hint}</span>`
    r.addEventListener('pointerenter', () => { r.style.background = '#fde68a55' })
    r.addEventListener('pointerleave', () => { r.style.background = '' })
    r.addEventListener('click', () => { closeSpawnCascade(); onPick() })
    return r
  }
  const rebuild = () => {
    const q = search.value.trim().toLowerCase()
    const rows: HTMLDivElement[] = []
    rows.push(row('λ term…', '', () => {
      promptAt(at.sx, at.sy, 'λ-term, e.g. \\x. x x', (t) =>
        tryEdit(lab, () => { spawnTermAt(lab, region, t, world); lab.toast(`term added in '${region}'`) }))
    }))
    for (const [name, body] of ctx.relations) {
      if (q !== '' && !name.toLowerCase().includes(q)) continue
      rows.push(row(name, `/${body.boundary.length}`, () => {
        tryEdit(lab, () => { spawnRelAt(lab, region, name, body.boundary.length, world); lab.toast(`${name}/${body.boundary.length} placed in '${region}'`) })
      }))
    }
    listing.replaceChildren(...rows)
  }
  search.addEventListener('input', rebuild)
  search.addEventListener('keydown', (e) => { e.stopPropagation(); if (e.key === 'Escape') closeSpawnCascade() })
  rebuild()
  document.body.append(menu)
  setTimeout(() => search.focus(), 0)
}
