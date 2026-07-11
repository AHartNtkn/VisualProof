/**
 * ROUND 4 · C — infer-first. The system does the parameter work it can:
 * citing runs the occurrence matcher over the sheet — a unique occurrence
 * applies IMMEDIATELY (selection and argument wires derived, nothing picked);
 * several occurrences cycle as highlighted candidates (Tab/click cycles,
 * Enter applies, Esc cancels). Conversion leads with one-click normal-form
 * tactics; a custom target is the fallback. Fold already infers (shipped).
 * REFUSALS anchor in a speech bubble at the selection that caused them.
 */
import { boot, hitShapes, installBrush, promptAt } from './shared'
import { installUndoKey } from './prove'
import { applyCitation, citeFrom, citeIsClosed, citeOccurrences, emptySelAt, fregeCtx, occToSel, rightClickMenu, showcase4, type ParamPick } from './prove4'
import { applyConversion } from '../src/kernel/rules/conversion'
import { applyStep } from '../src/kernel/proof/step'
import { convertToHeadNormal, convertToWeakHeadNormal } from '../src/app/tactics'
import { inferFoldArgs } from '../src/app/define'
import { applyRelFold } from '../src/kernel/rules/reldef'
import { parseTerm } from '../src/kernel/term/parse'
import { FUEL } from './prove'
import type { Occurrence } from '../src/kernel/diagram/subgraph/match'
import type { DiagramWithBoundary } from '../src/kernel/diagram/boundary'

const ctx = fregeCtx()

boot('Round 4 · C — infer-first', 'citing matches the theorem itself: unique occurrence applies instantly; several cycle (Tab/click, Enter, Esc); refusals anchor at the selection', (lab) => {
  // refusal bubble anchored at the selection centroid (or last mouse point)
  let lastMouse = { sx: innerWidth / 2, sy: innerHeight / 2 }
  lab.canvas.addEventListener('pointermove', (e) => { lastMouse = { sx: e.clientX, sy: e.clientY } })
  let bubbleTimer: number | undefined
  const refuse = (text: string): void => {
    document.getElementById('refusal-bubble')?.remove()
    const at = (() => {
      let sx = 0, sy = 0, n = 0
      for (const h of brush.selected) {
        const p = h.kind === 'node' ? lab.engine.bodies.get(h.id)?.pos : h.kind === 'region' ? lab.engine.regions.get(h.id)?.center : null
        if (p) { sx += p.x * lab.view.scale + lab.view.offsetX; sy += p.y * lab.view.scale + lab.view.offsetY; n++ }
      }
      return n > 0 ? { sx: sx / n, sy: sy / n } : lastMouse
    })()
    const el = document.createElement('div')
    el.id = 'refusal-bubble'
    el.textContent = text
    el.style.cssText = `position:fixed;left:${Math.max(8, Math.min(innerWidth - 320, at.sx - 150))}px;top:${Math.max(40, at.sy - 64)}px;z-index:9;max-width:300px;background:#fef2f2;border:1.5px solid #dc2626;border-radius:8px;padding:6px 10px;font:12px system-ui;color:#991b1b;box-shadow:0 3px 10px #0003`
    document.body.append(el)
    clearTimeout(bubbleTimer)
    bubbleTimer = window.setTimeout(() => el.remove(), 6000)
  }
  const guarded = (fn: () => void): boolean => {
    try { fn(); return true } catch (e) { refuse(e instanceof Error ? e.message : String(e)); return false }
  }
  const brush = installBrush(lab, rightClickMenu(lab, () => brush, ctx, onPick, { citeBare: true, onRefuse: refuse }))
  installUndoKey(lab, brush)

  // occurrence cycling state
  let cycle: { name: string; direction: 'forward' | 'reverse'; from: DiagramWithBoundary; occs: Occurrence[]; k: number } | null = null
  const applyOcc = (): void => {
    const c = cycle!
    const occ = c.occs[c.k]!
    if (guarded(() => {
      lab.mutate(applyCitation(lab, ctx, c.name, c.direction, occToSel(c.from, occ, lab.d), occ.attachments))
      brush.clear()
      lab.toast(`cited '${c.name}' at occurrence ${c.k + 1}/${c.occs.length}`)
    })) cycle = null
  }
  window.addEventListener('keydown', (e) => {
    if (cycle === null) return
    if (e.key === 'Escape') { cycle = null; lab.toast('citation cancelled') }
    else if (e.key === 'Tab') { e.preventDefault(); cycle.k = (cycle.k + 1) % cycle.occs.length; lab.toast(`occurrence ${cycle.k + 1}/${cycle.occs.length} — Enter applies`) }
    else if (e.key === 'Enter') applyOcc()
  })
  lab.canvas.addEventListener('pointerdown', (e) => {
    if (cycle === null || e.button !== 0) return
    e.stopImmediatePropagation()
    cycle.k = (cycle.k + 1) % cycle.occs.length
    lab.toast(`occurrence ${cycle.k + 1}/${cycle.occs.length} — Enter applies`)
  }, { capture: true })
  lab.overlay((out) => {
    if (cycle === null) return
    const occ = cycle.occs[cycle.k]!
    for (const nid of occ.nodeMap.values()) out.push(...hitShapes(lab, { kind: 'node', id: nid }, '#7c3aed', 2.6))
    for (const wid of occ.wireMap.values()) out.push(...hitShapes(lab, { kind: 'wire', id: wid }, '#7c3aed', 2.6))
    for (const rid of occ.regionMap.values()) {
      if (lab.d.regions[rid] !== undefined && lab.d.regions[rid]!.kind !== 'sheet') out.push(...hitShapes(lab, { kind: 'region', id: rid }, '#7c3aed', 2.2))
    }
  })

  function onPick(p: ParamPick): void {
    if (p.kind === 'cite') {
      const from = citeFrom(ctx, p.name, p.direction)
      if (citeIsClosed(from)) {
        guarded(() => {
          lab.mutate(applyCitation(lab, ctx, p.name, p.direction, emptySelAt(lab.d, lab.d.root), []))
          brush.clear()
          lab.toast(`cited '${p.name}' (closed — inserted at the sheet)`)
        })
        return
      }
      guarded(() => {
        const occs = citeOccurrences(lab, from)
        if (occs.length === 0) throw new Error(`no occurrence of '${p.name}' (${p.direction} side) found on the sheet`)
        cycle = { name: p.name, direction: p.direction, from, occs, k: 0 }
        if (occs.length === 1) { applyOcc(); return }
        lab.toast(`${occs.length} occurrences of '${p.name}' — Tab/click cycles, Enter applies, Esc cancels`)
      })
    } else if (p.kind === 'convert') {
      // infer-first fallback chain: weak head → head → custom target. A step
      // refusing (already in that form) falls THROUGH — the next strategy is
      // the handling; only the final fallback surfaces its refusal.
      const attempt = (fn: () => void): boolean => { try { fn(); return true } catch { return false } }
      if (attempt(() => { lab.mutate(convertToWeakHeadNormal(lab.d, p.node, FUEL).diagram); brush.clear(); lab.toast('weak-head-normalized (right-click again for head normal / custom)') })) return
      if (attempt(() => { lab.mutate(convertToHeadNormal(lab.d, p.node, FUEL).diagram); brush.clear(); lab.toast('head-normalized') })) return
      promptAt(lastMouse.sx, lastMouse.sy, 'already normal — custom target term (βη-equal)', (t) =>
        guarded(() => {
          const conv = applyConversion(lab.d, p.node, parseTerm(t), FUEL)
          lab.mutate(conv.diagram)
          brush.clear()
          lab.toast('converted')
        }))
    } else if (p.kind === 'instantiate') {
      // which comprehension cannot be inferred — smallest possible ask
      promptAt(lastMouse.sx, lastMouse.sy, `relation (${[...ctx.relations.keys()].join(', ')})`, (name) =>
        guarded(() => {
          const comp = ctx.relations.get(name.trim())
          if (comp === undefined) throw new Error(`unknown relation '${name}'`)
          lab.mutate(applyStep(lab.d, { rule: 'comprehensionInstantiate', bubble: p.bubble, comp, attachments: [], binders: {} }, ctx))
          brush.clear()
          lab.toast(`instantiated '${name}'`)
        }))
    } else {
      // fold: args are inferred (shipped behavior); only the relation is asked
      promptAt(lastMouse.sx, lastMouse.sy, `fold into relation (${[...ctx.relations.keys()].join(', ')})`, (name) =>
        guarded(() => {
          const args = inferFoldArgs(lab.d, p.sel, name.trim(), ctx)
          lab.mutate(applyRelFold(lab.d, p.sel, name.trim(), args, ctx.relations))
          brush.clear()
          lab.toast(`folded into '${name}'`)
        }))
    }
  }
}, showcase4)
