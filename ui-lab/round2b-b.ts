/**
 * ROUND 2b · B — library panel. A collapsible sidebar: search on top, the
 * library below as namespace groups (collapsed by default — 11 groups instead
 * of 140 rows); a non-empty search flattens to ranked matches. Every row
 * drags out onto the sheet; drop point decides the region (cuts included).
 * The whole panel folds to a tab to reclaim the sheet.
 */
import { boot, promptAt, spawnRelAt, spawnTermAt, tryEdit } from './shared'
import { installComposite, installGhostDrag } from './composite'
import { libId, mkRecents, searchLibrary, syntheticLibrary, type LibEntry } from './library'

const LIB = syntheticLibrary()
const recents = mkRecents(5)

boot('Round 2b · B — library panel', 'browse namespaces or search; drag any row onto the sheet; « folds the panel away', (lab) => {
  installComposite(lab)

  const panel = document.createElement('div')
  panel.style.cssText = 'position:fixed;left:0;top:56px;bottom:28px;width:230px;z-index:7;background:#fffffff2;border-right:1px solid #ccc;font:13px system-ui;display:flex;flex-direction:column'
  document.body.append(panel)
  const tab = document.createElement('button')
  tab.textContent = '» library'
  tab.style.cssText = 'position:fixed;left:0;top:64px;z-index:7;font:12px system-ui;padding:4px 8px;border:1px solid #ccc;border-left:none;border-radius:0 6px 6px 0;background:#fff;cursor:pointer;display:none'
  tab.addEventListener('click', () => { panel.style.display = 'flex'; tab.style.display = 'none' })
  document.body.append(tab)

  const head = document.createElement('div')
  head.style.cssText = 'display:flex;gap:4px;padding:6px;border-bottom:1px solid #eee'
  const search = document.createElement('input')
  search.placeholder = 'search 140 relations…'
  search.style.cssText = 'flex:1;min-width:0;padding:4px 8px;border:1px solid #ccc;border-radius:6px;outline:none;font:13px system-ui'
  const fold = document.createElement('button')
  fold.textContent = '«'
  fold.title = 'fold the panel away'
  fold.style.cssText = 'font:13px system-ui;padding:2px 8px;border:1px solid #ccc;border-radius:6px;background:#fff;cursor:pointer'
  fold.addEventListener('click', () => { panel.style.display = 'none'; tab.style.display = 'block' })
  head.append(search, fold)
  const body = document.createElement('div')
  body.style.cssText = 'flex:1;overflow-y:auto;padding:4px'
  panel.append(head, body)

  const row = (e: LibEntry): HTMLDivElement => {
    const r = document.createElement('div')
    r.style.cssText = 'display:flex;justify-content:space-between;padding:3px 8px;border-radius:5px;cursor:grab;user-select:none'
    r.innerHTML = `<span>${e.name}</span><span style="color:#999">${e.ns}/${e.arity}</span>`
    r.addEventListener('pointerenter', () => { r.style.background = '#fde68a55' })
    r.addEventListener('pointerleave', () => { r.style.background = '' })
    installGhostDrag(lab, r, `${libId(e)}/${e.arity}`, (region, at) => {
      tryEdit(lab, () => {
        spawnRelAt(lab, region, libId(e), e.arity, at)
        recents.note(e)
        lab.toast(`${libId(e)}/${e.arity} placed in '${region}'`)
        rebuild()
      })
    })
    return r
  }
  const termRow = (): HTMLDivElement => {
    const r = document.createElement('div')
    r.textContent = 'λ term…  (drag out, then type)'
    r.style.cssText = 'padding:5px 8px;margin:2px 0 6px;border:1px dashed #d97706;border-radius:6px;cursor:grab;color:#92400e;user-select:none'
    installGhostDrag(lab, r, 'λ term…', (region, at, sx, sy) => {
      promptAt(sx, sy, 'λ-term, e.g. \\x. x x', (t) =>
        tryEdit(lab, () => { spawnTermAt(lab, region, t, at); lab.toast(`term added in '${region}'`) }))
    })
    return r
  }
  const rebuild = () => {
    const q = search.value.trim()
    const frag: HTMLElement[] = [termRow()]
    if (q !== '') {
      const found = searchLibrary(LIB, q)
      for (const e of found.slice(0, 40)) frag.push(row(e))
      if (found.length > 40) {
        const more = document.createElement('div')
        more.textContent = `…and ${found.length - 40} more`
        more.style.cssText = 'padding:4px 8px;color:#999'
        frag.push(more)
      }
      if (found.length === 0) {
        const none = document.createElement('div')
        none.textContent = 'no relation matches'
        none.style.cssText = 'padding:4px 8px;color:#999'
        frag.push(none)
      }
    } else {
      const rec = recents.list()
      if (rec.length > 0) {
        const h = document.createElement('div')
        h.textContent = 'recent'
        h.style.cssText = 'padding:2px 8px;color:#999;font-size:11px;text-transform:uppercase'
        frag.push(h, ...rec.map(row))
      }
      const byNs = new Map<string, LibEntry[]>()
      for (const e of LIB) { const g = byNs.get(e.ns) ?? []; g.push(e); byNs.set(e.ns, g) }
      for (const [ns, entries] of byNs) {
        const det = document.createElement('details')
        const sum = document.createElement('summary')
        sum.textContent = `${ns}  (${entries.length})`
        sum.style.cssText = 'padding:3px 6px;cursor:pointer;color:#374151'
        det.append(sum, ...entries.map(row))
        frag.push(det)
      }
    }
    body.replaceChildren(...frag)
  }
  search.addEventListener('input', rebuild)
  rebuild()
})
