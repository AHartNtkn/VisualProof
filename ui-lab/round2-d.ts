/**
 * ROUND 2 · D — the composite of the Round-2 verdicts (see composite.ts for
 * the full gesture set). Spawn here is the INTERIM flat palette; the real
 * spawn browser is Round 2b's question.
 */
import { boot, promptAt, spawnRelAt, spawnTermAt, tryEdit, REL_PALETTE } from './shared'
import { installComposite, installGhostDrag } from './composite'

boot('Round 2 · D — composite', 'drag joins · slash (or dbl-click, see ⚙) severs · Space cuts around · Shift+Space bubbles · drag selected node moves it · Delete dissolves', (lab) => {
  installComposite(lab)

  const palette = document.createElement('div')
  palette.style.cssText = 'position:fixed;left:8px;top:80px;z-index:7;display:flex;flex-direction:column;gap:6px;font:13px system-ui'
  document.body.append(palette)
  const chip = (label: string): HTMLDivElement => {
    const c = document.createElement('div')
    c.textContent = label
    c.style.cssText = 'padding:5px 10px;background:#fff;border:1px solid #bbb;border-radius:7px;cursor:grab;box-shadow:0 1px 4px #0002;user-select:none'
    palette.append(c)
    return c
  }
  installGhostDrag(lab, chip('λ term…'), 'λ term…', (region, at, sx, sy) => {
    promptAt(sx, sy, 'λ-term, e.g. \\x. x x', (t) =>
      tryEdit(lab, () => { spawnTermAt(lab, region, t, at); lab.toast(`term added in '${region}'`) }))
  })
  for (const r of REL_PALETTE) {
    installGhostDrag(lab, chip(`${r.name}/${r.arity}`), `${r.name}/${r.arity}`, (region, at) => {
      tryEdit(lab, () => { spawnRelAt(lab, region, r.name, r.arity, at); lab.toast(`${r.name}/${r.arity} placed in '${region}'`) })
    })
  }
})
