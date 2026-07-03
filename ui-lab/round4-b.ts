/**
 * ROUND 4 · B — in-place picking. No panel: the diagram is the form.
 * Citation argument wires get numbered badges as you click them (click again
 * to unpick); Enter commits, Esc cancels; the hint strip narrates. Conversion
 * is an inline input AT the node, prefilled with its term. Instantiate/fold
 * choose via a chip row at the selection. REFUSALS go to the status line.
 */
import { boot, hitShapes, installBrush, promptAt } from './shared'
import { installUndoKey } from './prove'
import { applyCitation, citeFrom, citeIsClosed, emptySelAt, fregeCtx, rightClickMenu, showcase4, type ParamPick } from './prove4'
import { applyConversion } from '../src/kernel/rules/conversion'
import { applyStep } from '../src/kernel/proof/step'
import { inferFoldArgs } from '../src/app/define'
import { applyRelFold } from '../src/kernel/rules/reldef'
import { parseTerm } from '../src/kernel/term/parse'
import { printTerm } from '../src/kernel/term/print'
import { FUEL } from './prove'
import type { SubgraphSelection } from '../src/kernel/diagram/subgraph/selection'
import type { WireId } from '../src/kernel/diagram/diagram'

const ctx = fregeCtx()

boot('Round 4 · B — in-place picking', 'the diagram is the form: numbered badges on argument wires, Enter commits, Esc cancels; refusals in the status line', (lab) => {
  let cite: { name: string; direction: 'forward' | 'reverse'; sel: SubgraphSelection | null; need: number; args: WireId[] } | null = null
  const hints = document.createElement('div')
  hints.style.cssText = 'position:fixed;left:50%;transform:translateX(-50%);bottom:34px;z-index:7;padding:4px 12px;background:#ffffffe8;border:1px solid #ccc;border-radius:999px;font:12px system-ui;color:#444;display:none'
  document.body.append(hints)
  const hint = (t: string | null) => {
    hints.style.display = t === null ? 'none' : 'block'
    if (t !== null) hints.textContent = t
  }
  const guarded = (fn: () => void): boolean => {
    try { fn(); return true } catch (e) { lab.toast(e instanceof Error ? e.message : String(e)); return false }
  }
  const brush = installBrush(lab, rightClickMenu(lab, () => brush, ctx, onPick, { onRefuse: (t) => lab.toast(t) }))
  installUndoKey(lab, brush)

  // during citation, wire clicks toggle badges instead of brushing
  lab.canvas.addEventListener('pointerdown', (e) => {
    if (cite === null || e.button !== 0) return
    const h = lab.hitAt(e.clientX, e.clientY)
    if (h?.kind !== 'wire') return
    e.stopImmediatePropagation()
    const i = cite.args.indexOf(h.id)
    if (i >= 0) cite.args.splice(i, 1); else cite.args.push(h.id)
    hint(`cite '${cite.name}': ${cite.args.length}/${cite.need} argument wires — Enter commits, Esc cancels`)
  }, { capture: true })
  window.addEventListener('keydown', (e) => {
    if (cite === null) return
    if (e.key === 'Escape') { cite = null; hint(null); return }
    if (e.key !== 'Enter') return
    const c = cite
    if (guarded(() => {
      if (c.sel === null) throw new Error('citing a rule-shaped theorem needs the occurrence selected first')
      lab.mutate(applyCitation(lab, ctx, c.name, c.direction, c.sel, c.args))
      brush.clear()
      lab.toast(`cited '${c.name}'`)
    })) { cite = null; hint(null) }
  })
  lab.overlay((out) => {
    if (cite === null) return
    cite.args.forEach((w, i) => {
      out.push(...hitShapes(lab, { kind: 'wire', id: w }, '#7c3aed', 3))
      // badge: the pick order, drawn at the wire's ∃/junction body when it has
      // one, else at the first leg end
      const b = lab.engine.bodies.get(`x:${w}`) ?? lab.engine.bodies.get(`j:${w}`)
      const at = b?.pos ?? lab.legs().find((g) => g.leg.wid === w)?.pa
      if (at) {
        out.push({ kind: 'circle', center: at, r: 3.6, fill: '#ede9fe', stroke: '#7c3aed', width: 1.4, insetColor: null, glow: null })
        out.push({ kind: 'label', center: at, text: String(i + 1), color: '#7c3aed', r: 3.6, font: '600 4px system-ui' })
      }
    })
  })

  const chipRow = (labels: string[], at: { sx: number; sy: number }, pick: (label: string) => void): void => {
    const rowEl = document.createElement('div')
    rowEl.style.cssText = `position:fixed;left:${Math.min(at.sx, innerWidth - 300)}px;top:${at.sy + 8}px;z-index:8;display:flex;gap:4px;flex-wrap:wrap;max-width:300px`
    for (const l of labels) {
      const c = document.createElement('button')
      c.textContent = l
      c.style.cssText = 'font:12px system-ui;padding:3px 9px;border:1px solid #d97706;border-radius:999px;background:#fff;cursor:pointer'
      c.addEventListener('click', () => { rowEl.remove(); pick(l) })
      rowEl.append(c)
    }
    const esc = (e: KeyboardEvent) => { if (e.key === 'Escape') { rowEl.remove(); window.removeEventListener('keydown', esc) } }
    window.addEventListener('keydown', esc)
    document.body.append(rowEl)
  }
  let lastMouse = { sx: innerWidth / 2, sy: innerHeight / 2 }
  lab.canvas.addEventListener('pointermove', (e) => { lastMouse = { sx: e.clientX, sy: e.clientY } })

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
      cite = { name: p.name, direction: p.direction, sel: p.sel, need: from.boundary.length, args: [] }
      hint(`cite '${p.name}': click ${from.boundary.length} argument wires in boundary order — Enter commits, Esc cancels`)
    } else if (p.kind === 'convert') {
      const node = lab.d.nodes[p.node]!
      const b = lab.engine.bodies.get(p.node)
      const sx = b ? b.pos.x * lab.view.scale + lab.view.offsetX : lastMouse.sx
      const sy = b ? b.pos.y * lab.view.scale + lab.view.offsetY : lastMouse.sy
      promptAt(sx, sy, 'target term (βη-equal)', (t) =>
        guarded(() => {
          const conv = applyConversion(lab.d, p.node, parseTerm(t === '' && node.kind === 'term' ? printTerm(node.term) : t), FUEL)
          lab.mutate(conv.diagram)
          brush.clear()
          lab.toast('converted')
        }))
    } else if (p.kind === 'instantiate') {
      chipRow([...ctx.relations.keys()], lastMouse, (name) => {
        guarded(() => {
          lab.mutate(applyStep(lab.d, { rule: 'comprehensionInstantiate', bubble: p.bubble, comp: ctx.relations.get(name)!, attachments: [], binders: {} }, ctx))
          brush.clear()
          lab.toast(`instantiated '${name}'`)
        })
      })
    } else {
      chipRow([...ctx.relations.keys()], lastMouse, (name) => {
        guarded(() => {
          const args = inferFoldArgs(lab.d, p.sel, name, ctx)
          lab.mutate(applyRelFold(lab.d, p.sel, name, args, ctx.relations))
          brush.clear()
          lab.toast(`folded into '${name}'`)
        })
      })
    }
  }
}, showcase4)
