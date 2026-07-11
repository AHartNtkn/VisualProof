/**
 * ROUND 3 · D — the streamlined verdict: dedicated mechanics, no menu.
 *  - DELETE/Backspace = contextual deletion: double-cut elim on a double cut,
 *    dissolve on a vacuous bubble, erasure in positive regions, deiteration
 *    elsewhere — one key, interpreted by the selection (kernel still rules).
 *  - W = wrap in a double cut; Shift+W = wrap in a vacuous bubble.
 *  - DRAG the selection into a glowing region = iterate (round-3-C's gesture).
 *  - The hint strip says what each binding means for THIS selection.
 *  - The MEMORY box (bottom right) shows what Ctrl+Z would restore — the
 *    preview inverted: make the move, see what you left behind.
 */
import { boot, installBrush } from './shared'
import { commit, deleteInterpretation, discover, installUndoKey, iterationTargets, proveShowcase, renderPreview } from './prove'
import type { ActionDescriptor } from '../src/app/actions'
import type { SubgraphSelection } from '../src/kernel/diagram/subgraph/selection'
import type { Diagram, RegionId } from '../src/kernel/diagram/diagram'
import type { Vec2 } from '../src/view/vec'

boot('Round 3 · D — dedicated mechanics', 'Delete = contextual deletion · W / Shift+W = double-cut / bubble wrap · drag selection = iterate · box = what Ctrl+Z restores', (lab) => {
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

  // ---- the memory box: renders what Ctrl+Z would restore ----
  const memory = document.createElement('div')
  memory.style.cssText = 'position:fixed;right:8px;bottom:34px;z-index:7;display:none;background:#fff;border:1.5px solid #92400e;border-radius:8px;box-shadow:0 4px 16px #0003;font:12px system-ui'
  const memoryLabel = document.createElement('div')
  memoryLabel.style.cssText = 'padding:3px 8px;color:#92400e;border-bottom:1px solid #eee'
  const memoryCanvas = document.createElement('canvas')
  memoryCanvas.width = 300; memoryCanvas.height = 210
  memory.append(memoryLabel, memoryCanvas)
  document.body.append(memory)
  let memoryShown: Diagram | null = null
  let lastMove = ''
  lab.onFrame(() => {
    const prev = lab.peekUndo()
    if (prev === null) { memory.style.display = 'none'; memoryShown = null; return }
    if (prev.d !== memoryShown) {
      memoryShown = prev.d
      renderPreview(memoryCanvas, prev.d, prev.boundary.filter((w) => prev.d.wires[w] !== undefined))
      memoryLabel.textContent = lastMove === '' ? 'before (Ctrl+Z restores this)' : `before ${lastMove} (Ctrl+Z restores this)`
    }
    memory.style.display = 'block'
  })

  // ---- dedicated keys ----
  window.addEventListener('keydown', (e) => {
    if (document.activeElement instanceof HTMLInputElement) return
    if (e.key === 'Delete' || e.key === 'Backspace') {
      const disc = discover(lab, brush.selected)
      if (disc === null) { lab.toast(brush.selected.length === 0 ? 'select what to delete first' : 'this selection spans several regions; pick within one region'); return }
      const a = deleteInterpretation(lab, disc)
      if (a === null) { lab.toast('nothing here reads as a deletion'); return }
      if (commit(lab, brush, disc.sel, a)) lastMove = `[${a.label}]`
    } else if (e.key === 'w' || e.key === 'W') {
      const disc = discover(lab, brush.selected)
      if (disc === null) { lab.toast('select what to wrap first'); return }
      const a = disc.actions.find((x) => x.kind === (e.shiftKey ? 'vacuousWrap' : 'doubleCutWrap'))
      if (a === undefined) { lab.toast('that wrap does not apply here'); return }
      if (commit(lab, brush, disc.sel, a) || a.kind === 'vacuousWrap') lastMove = `[${a.label}]`
    }
  })

  // ---- drag-to-iterate (round-3-C's gesture, previews removed) ----
  lab.canvas.addEventListener('pointermove', (e) => {
    if (iterDrag === null) return
    iterDrag.cursor = lab.toWorld(e.clientX, e.clientY)
    const r = lab.regionAt(iterDrag.cursor)
    iterDrag.over = iterDrag.targets.includes(r) ? r : null
  })
  lab.canvas.addEventListener('pointerup', () => {
    if (iterDrag === null) return
    const it = iterDrag
    iterDrag = null
    if (it.over === null) { lab.toast('release inside a glowing region to iterate (selection unchanged)'); return }
    if (commit(lab, brush, it.sel, it.a, it.over)) lastMove = `[iterate into '${it.over}']`
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

  // ---- hint strip: what the bindings mean for THIS selection ----
  const hints = document.createElement('div')
  hints.style.cssText = 'position:fixed;left:50%;transform:translateX(-50%);bottom:34px;z-index:7;padding:4px 12px;background:#ffffffe8;border:1px solid #ccc;border-radius:999px;font:12px system-ui;color:#444'
  document.body.append(hints)
  let lastSig: string | null = null
  lab.onFrame(() => {
    const sig = brush.selected.map((h) => `${h.kind}:${h.id}`).sort().join(',')
    if (sig === lastSig) return
    lastSig = sig
    const disc = discover(lab, brush.selected)
    if (disc === null) {
      hints.textContent = brush.selected.length === 0 ? 'select something — Delete, W, and drag act on the selection' : 'selection spans several regions'
      return
    }
    const del = deleteInterpretation(lab, disc)
    const parts = [
      `Delete → ${del === null ? '—' : del.label}`,
      'W → double-cut wrap',
      'Shift+W → bubble wrap',
      disc.actions.some((a) => a.kind === 'iterate') ? 'drag → iterate' : null,
    ].filter((x): x is string => x !== null)
    hints.textContent = parts.join('  ·  ')
  })
}, proveShowcase)
