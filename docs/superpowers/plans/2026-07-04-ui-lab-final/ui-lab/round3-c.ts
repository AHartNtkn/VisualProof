/**
 * ROUND 3 · C — ghost previews. Applicable moves appear as chips floating by
 * the selection; HOVERING a chip renders the diagram the rule would produce
 * in an inset (the real pipeline, miniaturized) — you see the result before
 * committing. Iterate has a direct gesture: DRAG the selection; legal target
 * regions glow, hovering one previews that iteration, releasing commits.
 */
import { boot, installBrush } from './shared'
import { commit, discover, installUndoKey, iterationTargets, proveShowcase, renderPreview, tryAction } from './prove'
import type { ActionDescriptor } from '../src/app/actions'
import type { SubgraphSelection } from '../src/kernel/diagram/subgraph/selection'
import type { RegionId } from '../src/kernel/diagram/diagram'
import type { Vec2 } from '../src/view/vec'

boot('Round 3 · C — ghost previews', 'chips by the selection; hover = preview the RESULT; drag the selection into a region to iterate', (lab) => {
  let iterDrag: { sel: SubgraphSelection; a: ActionDescriptor; targets: RegionId[]; cursor: Vec2; over: RegionId | null } | null = null
  const brush = installBrush(lab, (h, e) => {
    if (e.button !== 0 || h?.kind !== 'node' || !brush.isSelected(h)) return false
    const disc = discover(lab, brush.selected)
    const a = disc?.actions.find((x) => x.kind === 'iterate')
    if (disc === null || a === undefined) return false
    iterDrag = { sel: disc.sel, a, targets: iterationTargets(lab, disc.sel), cursor: lab.toWorld(e.clientX, e.clientY), over: null }
    return true
  })
  installUndoKey(lab, brush)

  // ---- preview inset ----
  const inset = document.createElement('div')
  inset.style.cssText = 'position:fixed;right:8px;bottom:34px;z-index:7;display:none;background:#fff;border:1.5px solid #16a34a;border-radius:8px;box-shadow:0 4px 16px #0003;font:12px system-ui'
  const insetLabel = document.createElement('div')
  insetLabel.style.cssText = 'padding:3px 8px;color:#166534;border-bottom:1px solid #eee'
  const insetCanvas = document.createElement('canvas')
  insetCanvas.width = 300; insetCanvas.height = 210
  inset.append(insetLabel, insetCanvas)
  document.body.append(inset)
  let previewKey = ''
  const showPreview = (sel: SubgraphSelection, a: ActionDescriptor, label: string, target?: RegionId): void => {
    const key = `${a.kind}:${target ?? ''}:${brush.selected.map((h) => h.id).join(',')}`
    if (key !== previewKey) {
      previewKey = key
      const next = tryAction(lab, sel, a, target)
      if (next === null) { inset.style.display = 'none'; return }
      renderPreview(insetCanvas, next, lab.boundary.filter((w) => next.wires[w] !== undefined))
      insetLabel.textContent = `after: ${label}`
    }
    inset.style.display = 'block'
  }
  const hidePreview = (): void => { inset.style.display = 'none'; previewKey = '' }

  // ---- chip bar (applicable moves by the selection) ----
  const bar = document.createElement('div')
  bar.style.cssText = 'position:fixed;z-index:7;display:none;gap:4px;padding:4px;background:#ffffffe8;border:1px solid #ccc;border-radius:8px;font:12px system-ui;box-shadow:0 2px 8px #0002;flex-wrap:wrap;max-width:420px'
  document.body.append(bar)
  let lastSig = ''
  const rebuildChips = (): void => {
    const disc = discover(lab, brush.selected)
    bar.replaceChildren()
    if (disc === null) { bar.style.display = 'none'; hidePreview(); return }
    const usable = disc.actions.filter((a) => a.kind !== 'insert' && a.kind !== 'convert' && a.kind !== 'instantiate' && a.kind !== 'relFold' && a.kind !== 'citeTheorem')
    if (usable.length === 0) { bar.style.display = 'none'; hidePreview(); return }
    for (const a of usable) {
      const chip = document.createElement('button')
      chip.textContent = a.kind === 'iterate' ? 'iterate (drag the selection)' : a.label
      chip.style.cssText = 'font:12px system-ui;padding:3px 8px;border:1px solid #bbb;border-radius:999px;background:#fff;cursor:pointer'
      chip.addEventListener('pointerdown', (e) => e.stopPropagation())
      if (a.kind !== 'iterate') {
        chip.addEventListener('pointerenter', () => showPreview(disc.sel, a, a.label))
        chip.addEventListener('pointerleave', hidePreview)
        chip.addEventListener('click', () => { hidePreview(); commit(lab, brush, disc.sel, a) })
      } else {
        chip.style.color = '#666'
        chip.addEventListener('click', () => lab.toast('iterate directly: drag any selected node into a green region'))
      }
      bar.append(chip)
    }
    bar.style.display = 'flex'
  }
  lab.onFrame(() => {
    const sig = brush.selected.map((h) => `${h.kind}:${h.id}`).sort().join(',')
    if (sig !== lastSig) { lastSig = sig; rebuildChips() }
    if (bar.style.display === 'none') return
    // above the selection's TOP edge, never over it — a covered node would
    // swallow the drag-to-iterate pointerdown
    let sx = 0, minTop = Infinity, n = 0
    for (const h of brush.selected) {
      const p = h.kind === 'node' ? lab.engine.bodies.get(h.id)?.pos : h.kind === 'region' ? lab.engine.regions.get(h.id)?.center : null
      const r = h.kind === 'node' ? lab.engine.bodies.get(h.id)?.discR ?? 0 : h.kind === 'region' ? lab.engine.regions.get(h.id)?.radius ?? 0 : 0
      if (p) { sx += p.x; minTop = Math.min(minTop, p.y - r); n++ }
    }
    if (n === 0) return
    const px = (sx / n) * lab.view.scale + lab.view.offsetX
    const py = minTop * lab.view.scale + lab.view.offsetY
    bar.style.left = `${Math.max(8, Math.min(innerWidth - 440, px - 160))}px`
    bar.style.top = `${Math.max(40, py - 44)}px`
  })

  // ---- drag-to-iterate with per-target preview ----
  lab.canvas.addEventListener('pointermove', (e) => {
    if (iterDrag === null) return
    iterDrag.cursor = lab.toWorld(e.clientX, e.clientY)
    const r = lab.regionAt(iterDrag.cursor)
    iterDrag.over = iterDrag.targets.includes(r) ? r : null
    if (iterDrag.over !== null) showPreview(iterDrag.sel, iterDrag.a, `iterate into '${iterDrag.over}'`, iterDrag.over)
    else hidePreview()
  })
  lab.canvas.addEventListener('pointerup', () => {
    if (iterDrag === null) return
    const it = iterDrag
    iterDrag = null
    hidePreview()
    if (it.over === null) { lab.toast('release inside a green region to iterate (selection unchanged)'); return }
    commit(lab, brush, it.sel, it.a, it.over)
  })
  lab.overlay((out) => {
    if (iterDrag === null) return
    for (const r of iterDrag.targets) {
      if (lab.d.regions[r]!.kind === 'sheet') continue
      const g = lab.engine.regions.get(r)
      if (g) {
        const isOver = r === iterDrag.over
        out.push({ kind: 'circle', center: g.center, r: g.radius, fill: isOver ? '#16a34a22' : '#16a34a10', stroke: '#16a34a', width: isOver ? 2.4 : 1.4, insetColor: null, glow: null })
      }
    }
  })
}, proveShowcase)
