/**
 * ROUND 4 · A — staged panel. Every parameterized move opens a right-side
 * panel that walks its parameters explicitly: citation shows the argument
 * wires as an ordered chip list you fill by clicking the diagram; conversion
 * prefives the node's term for editing plus one-click normal-form tactics;
 * instantiation lists the relations. REFUSALS render inside the panel, red,
 * anchored to the flow that caused them.
 */
import { boot, installBrush } from './shared'
import { installUndoKey } from './prove'
import { applyCitation, citeFrom, citeIsClosed, emptySelAt, fregeCtx, rightClickMenu, showcase4, type ParamPick } from './prove4'
import { applyConversion } from '../src/kernel/rules/conversion'
import { applyStep } from '../src/kernel/proof/step'
import { convertToHeadNormal, convertToWeakHeadNormal } from '../src/app/tactics'
import { inferFoldArgs } from '../src/app/define'
import { applyRelFold } from '../src/kernel/rules/reldef'
import { parseTerm } from '../src/kernel/term/parse'
import { printTerm } from '../src/kernel/term/print'
import { FUEL } from './prove'
import type { WireId } from '../src/kernel/diagram/diagram'

const ctx = fregeCtx()

boot('Round 4 · A — staged panel', 'right-click a selection for parameterized moves; a panel walks the parameters; refusals live in the panel', (lab) => {
  const panel = document.createElement('div')
  panel.style.cssText = 'position:fixed;right:8px;top:44px;z-index:7;width:270px;background:#fff;border:1.5px solid #d97706;border-radius:8px;box-shadow:0 4px 16px #0003;font:13px system-ui;display:none;padding:8px'
  document.body.append(panel)
  const closePanel = () => { panel.style.display = 'none'; panel.replaceChildren(); wirePick = null }
  const refuse = (text: string) => {
    let err = panel.querySelector('.err') as HTMLDivElement | null
    if (err === null || panel.style.display === 'none') { lab.toast(text); return }
    err.textContent = text
  }
  const el = (tag: string, css: string, text = ''): HTMLElement => {
    const x = document.createElement(tag)
    x.style.cssText = css
    if (text) x.textContent = text
    return x
  }
  const btn = (label: string, onClick: () => void): HTMLButtonElement => {
    const b = el('button', 'font:13px system-ui;padding:4px 10px;border:1px solid #bbb;border-radius:6px;background:#fff;cursor:pointer;margin:2px 4px 2px 0') as HTMLButtonElement
    b.textContent = label
    b.addEventListener('click', onClick)
    return b
  }
  const errLine = (): HTMLElement => { const e = el('div', 'color:#dc2626;min-height:1.2em;margin-top:6px;white-space:pre-wrap'); e.className = 'err'; return e }

  let wirePick: { args: WireId[]; onChange: () => void } | null = null
  const brush = installBrush(lab, rightClickMenu(lab, () => brush, ctx, onPick, { onRefuse: refuse }))
  installUndoKey(lab, brush)
  // during an argument-pick phase, wire clicks feed the panel, not the brush
  lab.canvas.addEventListener('pointerdown', (e) => {
    if (wirePick === null) return
    const h = lab.hitAt(e.clientX, e.clientY)
    if (h?.kind !== 'wire') return
    e.stopImmediatePropagation()
    const i = wirePick.args.indexOf(h.id)
    if (i >= 0) wirePick.args.splice(i, 1); else wirePick.args.push(h.id)
    wirePick.onChange()
  }, { capture: true })

  function onPick(p: ParamPick): void {
    panel.replaceChildren()
    panel.style.display = 'block'
    if (p.kind === 'cite') {
      const from = citeFrom(ctx, p.name, p.direction)
      panel.append(el('b', '', `cite '${p.name}' (${p.direction})`))
      if (citeIsClosed(from)) {
        panel.append(el('div', 'color:#666;margin:6px 0', 'closed statement — no arguments; inserts at the sheet'))
        panel.append(btn('Commit', () => {
          guarded(() => {
            lab.mutate(applyCitation(lab, ctx, p.name, p.direction, emptySelAt(lab.d, lab.d.root), []))
            brush.clear()
            closePanel()
            lab.toast(`cited '${p.name}'`)
          })
        }))
      } else {
        const need = from.boundary.length
        const list = el('div', 'margin:6px 0;color:#333')
        const pick = { args: [] as WireId[], onChange: () => render() }
        wirePick = pick
        const render = () => {
          list.replaceChildren(el('div', 'color:#666', `argument wires — click ${need} in boundary order:`))
          pick.args.forEach((w, i) => list.append(el('div', 'padding:1px 6px', `${i + 1}. ${w}  (click again to unpick)`)))
        }
        render()
        panel.append(list)
        panel.append(btn('Commit', () => {
          guarded(() => {
            if (p.sel === null) throw new Error('citing a rule-shaped theorem needs the occurrence selected first')
            lab.mutate(applyCitation(lab, ctx, p.name, p.direction, p.sel, pick.args))
            brush.clear()
            closePanel()
            lab.toast(`cited '${p.name}'`)
          })
        }))
      }
    } else if (p.kind === 'convert') {
      panel.append(el('b', '', 'convert (βη)'))
      const node = lab.d.nodes[p.node]!
      const input = el('input', 'width:100%;box-sizing:border-box;margin:6px 0;padding:4px 8px;border:1px solid #ccc;border-radius:6px;font:13px system-ui') as HTMLInputElement
      input.value = node.kind === 'term' ? printTerm(node.term) : ''
      panel.append(el('div', 'color:#666', 'target term (βη-equal):'), input)
      panel.append(btn('Convert to target', () => {
        guarded(() => {
          const conv = applyConversion(lab.d, p.node, parseTerm(input.value), FUEL)
          lab.mutate(conv.diagram)
          brush.clear(); closePanel(); lab.toast('converted')
        })
      }))
      panel.append(btn('→ head normal', () => {
        guarded(() => { lab.mutate(convertToHeadNormal(lab.d, p.node, FUEL).diagram); brush.clear(); closePanel(); lab.toast('head-normalized') })
      }))
      panel.append(btn('→ weak head', () => {
        guarded(() => { lab.mutate(convertToWeakHeadNormal(lab.d, p.node, FUEL).diagram); brush.clear(); closePanel(); lab.toast('weak-head-normalized') })
      }))
    } else if (p.kind === 'instantiate') {
      panel.append(el('b', '', 'instantiate the relation'))
      panel.append(el('div', 'color:#666;margin:6px 0', 'choose which comprehension the bubble instantiates:'))
      for (const [name, comp] of ctx.relations) {
        panel.append(btn(name, () => {
          guarded(() => {
            lab.mutate(applyStep(lab.d, { rule: 'comprehensionInstantiate', bubble: p.bubble, comp, attachments: [], binders: {} }, ctx))
            brush.clear(); closePanel(); lab.toast(`instantiated '${name}'`)
          })
        }))
      }
    } else {
      panel.append(el('b', '', 'fold into a relation'))
      panel.append(el('div', 'color:#666;margin:6px 0', 'argument wires are inferred by occurrence matching:'))
      for (const name of ctx.relations.keys()) {
        panel.append(btn(name, () => {
          guarded(() => {
            const args = inferFoldArgs(lab.d, p.sel, name, ctx)
            lab.mutate(applyRelFold(lab.d, p.sel, name, args, ctx.relations))
            brush.clear(); closePanel(); lab.toast(`folded into '${name}'`)
          })
        }))
      }
    }
    panel.append(errLine(), btn('Cancel', closePanel))
    function guarded(fn: () => void): void {
      try { fn() } catch (e) { refuse(e instanceof Error ? e.message : String(e)) }
    }
  }
}, showcase4)
