/**
 * ROUND 4 · D — the verdict composite. Infer-first everywhere (4c's model):
 *  - CITE: the menu lists ONLY theorems that apply here — with a selection,
 *    only those whose occurrence CONTAINS it (brushing the wires along with
 *    the nodes cannot matter). One occurrence applies instantly; several
 *    Tab/click-cycle, Enter applies. Argument order is never asked.
 *  - CONVERT: double-click a term = normalize; the menu keeps → head normal
 *    and → custom target.
 *  - INSTANTIATE: splices the relation's REF — it stays FOLDED; unfolding is
 *    a later, selective move. (The anonymous-comprehension construction box
 *    is queued as its own design item.)
 *  - Ctrl+drag = physics-only handle (shared; no proof meaning).
 *  - Refusals anchor at the selection; the memory box shows Ctrl+Z's target.
 */
import { boot, hitShapes, installBrush, promptAt } from './shared'
import { installUndoKey, renderPreview } from './prove'
import { applyCitation, citeCandidates, emptySelAt, foldedComp, fregeCtx, occToSel, showcase4, type CiteCandidate } from './prove4'
import { discover } from './prove'
import { applyConversion } from '../src/kernel/rules/conversion'
import { applyStep } from '../src/kernel/proof/step'
import { convertToHeadNormal, convertToWeakHeadNormal } from '../src/app/tactics'
import { inferFoldArgs } from '../src/app/define'
import { applyRelFold } from '../src/kernel/rules/reldef'
import { parseTerm } from '../src/kernel/term/parse'
import { polarity } from '../src/kernel/diagram/regions'
import { FUEL } from './prove'
import type { Diagram, NodeId } from '../src/kernel/diagram/diagram'

const ctx = fregeCtx()

boot('Round 4 · D — verdict composite', 'menu lists only what applies; selection disambiguates; dbl-click normalizes; instantiate stays folded; Ctrl+drag = physics', (lab) => {
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

  // ---- right-click detection + the context-filtered menu ----
  let rightDown: { sx: number; sy: number } | null = null
  let menu: HTMLDivElement | null = null
  const closeMenu = () => { menu?.remove(); menu = null }
  const brush = installBrush(lab, (_h, e) => {
    if (e.button !== 2) return false
    rightDown = { sx: e.clientX, sy: e.clientY }
    return true
  })
  installUndoKey(lab, brush)
  lab.canvas.addEventListener('contextmenu', (e) => e.preventDefault())
  lab.canvas.addEventListener('pointerdown', () => closeMenu())
  window.addEventListener('keydown', (e) => { if (e.key === 'Escape') closeMenu() })
  lab.canvas.addEventListener('pointerup', (e) => {
    if (rightDown === null) return
    const rd = rightDown
    rightDown = null
    if (Math.hypot(e.clientX - rd.sx, e.clientY - rd.sy) > 4) return
    openMenu(rd)
  })
  function openMenu(at: { sx: number; sy: number }): void {
    closeMenu()
    const disc = discover(lab, brush.selected, ctx)
    menu = document.createElement('div')
    menu.style.cssText = `position:fixed;left:${Math.min(at.sx, innerWidth - 280)}px;top:${Math.min(at.sy, innerHeight - 380)}px;z-index:8;width:260px;background:#fff;border:1.5px solid #d97706;border-radius:8px;box-shadow:0 4px 16px #0003;font:13px system-ui;max-height:360px;overflow-y:auto`
    const row = (label: string, onClick: (() => void) | null): void => {
      const r = document.createElement('div')
      r.textContent = label
      r.style.cssText = `padding:6px 10px;${onClick ? 'cursor:pointer' : 'color:#999;font-size:11px;text-transform:uppercase;border-top:1px solid #eee'}`
      if (onClick) {
        r.addEventListener('pointerenter', () => { r.style.background = '#fde68a55' })
        r.addEventListener('pointerleave', () => { r.style.background = '' })
        r.addEventListener('click', () => { closeMenu(); onClick() })
      }
      menu!.append(r)
    }
    if (disc !== null) {
      for (const a of disc.actions) {
        if (a.kind === 'convert') {
          const node = disc.sel.nodes[0]!
          row('Normalize (also: double-click)', () => normalize(node))
          row('Convert → head normal', () => { guarded(() => { lab.mutate(convertToHeadNormal(lab.d, node, FUEL).diagram); brush.clear(); lab.toast('head-normalized') }) })
          row('Convert → custom target…', () => {
            promptAt(lastMouse.sx, lastMouse.sy, 'target term (βη-equal)', (t) =>
              guarded(() => { lab.mutate(applyConversion(lab.d, node, parseTerm(t), FUEL).diagram); brush.clear(); lab.toast('converted') }))
          })
        } else if (a.kind === 'instantiate') {
          const bubble = disc.sel.regions[0]!
          for (const name of ctx.relations.keys()) {
            row(`Instantiate ${name} (stays folded)`, () => {
              guarded(() => {
                lab.mutate(applyStep(lab.d, { rule: 'comprehensionInstantiate', bubble, comp: foldedComp(ctx, name), attachments: [], binders: {} }, ctx))
                brush.clear()
                lab.toast(`instantiated '${name}' — still folded; unfold selectively later`)
              })
            })
          }
        } else if (a.kind === 'relUnfold') {
          row(a.label, () => {
            guarded(() => { lab.mutate(applyStep(lab.d, { rule: 'relUnfold', node: disc.sel.nodes[0]! }, ctx)); brush.clear(); lab.toast('unfolded') })
          })
        } else if (a.kind === 'relFold') {
          row('Fold into…', () => {
            promptAt(lastMouse.sx, lastMouse.sy, `relation (${[...ctx.relations.keys()].join(', ')})`, (name) =>
              guarded(() => {
                const args = inferFoldArgs(lab.d, disc.sel, name.trim(), ctx)
                lab.mutate(applyRelFold(lab.d, disc.sel, name.trim(), args, ctx.relations))
                brush.clear()
                lab.toast(`folded into '${name}'`)
              }))
          })
        }
      }
    }
    const direction = disc === null ? 'forward' as const : polarity(lab.d, disc.sel.region) === 'positive' ? 'forward' as const : 'reverse' as const
    const cands = citeCandidates(lab, ctx, disc === null ? [] : brush.selected, direction)
    if (cands.applicable.length > 0) {
      row(disc === null ? 'applicable here' : 'applicable to the selection', null)
      for (const c of cands.applicable) {
        row(`${c.name}  (${c.occs!.length === 1 ? 'applies' : `${c.occs!.length} places`}, ${direction})`, () => beginCite(c))
      }
    }
    row('insert (closed statements)', null)
    for (const c of cands.closed) {
      row(c.name, () => {
        guarded(() => {
          lab.mutate(applyCitation(lab, ctx, c.name, c.direction, emptySelAt(lab.d, lab.d.root), []))
          brush.clear()
          lab.toast(`cited '${c.name}' (closed — inserted at the sheet)`)
        })
      })
    }
    document.body.append(menu)
  }

  // ---- occurrence cycling (unique applies instantly) ----
  let cycle: { c: CiteCandidate; k: number } | null = null
  const applyOcc = (): void => {
    const cy = cycle!
    const occ = cy.c.occs![cy.k]!
    if (guarded(() => {
      lab.mutate(applyCitation(lab, ctx, cy.c.name, cy.c.direction, occToSel(cy.c.from, occ, lab.d), occ.attachments))
      brush.clear()
      lab.toast(`cited '${cy.c.name}'`)
    })) cycle = null
  }
  function beginCite(c: CiteCandidate): void {
    cycle = { c, k: 0 }
    if (c.occs!.length === 1) { applyOcc(); return }
    lab.toast(`${c.occs!.length} occurrences of '${c.name}' — Tab/click cycles, Enter applies, Esc cancels`)
  }
  window.addEventListener('keydown', (e) => {
    if (cycle === null) return
    if (e.key === 'Escape') { cycle = null; lab.toast('citation cancelled') }
    else if (e.key === 'Tab') { e.preventDefault(); cycle.k = (cycle.k + 1) % cycle.c.occs!.length; lab.toast(`occurrence ${cycle.k + 1}/${cycle.c.occs!.length} — Enter applies`) }
    else if (e.key === 'Enter') applyOcc()
  })
  lab.canvas.addEventListener('pointerdown', (e) => {
    if (cycle === null || e.button !== 0 || e.ctrlKey) return
    e.stopImmediatePropagation()
    cycle.k = (cycle.k + 1) % cycle.c.occs!.length
    lab.toast(`occurrence ${cycle.k + 1}/${cycle.c.occs!.length} — Enter applies`)
  }, { capture: true })
  lab.overlay((out) => {
    if (cycle === null) return
    const occ = cycle.c.occs![cycle.k]!
    for (const nid of occ.nodeMap.values()) out.push(...hitShapes(lab, { kind: 'node', id: nid }, '#7c3aed', 2.6))
    for (const wid of occ.wireMap.values()) out.push(...hitShapes(lab, { kind: 'wire', id: wid }, '#7c3aed', 2.6))
  })

  // ---- double-click a term node = normalize (weak head, then head) ----
  function normalize(node: NodeId): void {
    const attempt = (fn: () => void): boolean => { try { fn(); return true } catch { return false } }
    if (attempt(() => { lab.mutate(convertToWeakHeadNormal(lab.d, node, FUEL).diagram); brush.clear(); lab.toast('normalized (weak head)') })) return
    if (attempt(() => { lab.mutate(convertToHeadNormal(lab.d, node, FUEL).diagram); brush.clear(); lab.toast('normalized (head)') })) return
    refuse('already in normal form — use Convert → custom target for a specific βη-equal shape')
  }
  lab.canvas.addEventListener('dblclick', (e) => {
    const h = lab.hitAt(e.clientX, e.clientY)
    if (h?.kind !== 'node') return
    if (lab.d.nodes[h.id]!.kind !== 'term') return
    normalize(h.id)
  })

  // ---- the memory box (round-3 verdict) ----
  const memory = document.createElement('div')
  memory.style.cssText = 'position:fixed;right:8px;bottom:34px;z-index:7;display:none;background:#fff;border:1.5px solid #92400e;border-radius:8px;box-shadow:0 4px 16px #0003;font:12px system-ui'
  const memoryLabel = document.createElement('div')
  memoryLabel.style.cssText = 'padding:3px 8px;color:#92400e;border-bottom:1px solid #eee'
  memoryLabel.textContent = 'before (Ctrl+Z restores this)'
  const memoryCanvas = document.createElement('canvas')
  memoryCanvas.width = 300; memoryCanvas.height = 210
  memory.append(memoryLabel, memoryCanvas)
  document.body.append(memory)
  let memoryShown: Diagram | null = null
  lab.onFrame(() => {
    const prev = lab.peekUndo()
    if (prev === null) { memory.style.display = 'none'; memoryShown = null; return }
    if (prev.d !== memoryShown) {
      memoryShown = prev.d
      renderPreview(memoryCanvas, prev.d, prev.boundary.filter((w) => prev.d.wires[w] !== undefined))
    }
    memory.style.display = 'block'
  })
}, showcase4)
