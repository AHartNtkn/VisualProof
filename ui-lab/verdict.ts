/**
 * The VERDICT move layer, step-emitting: everything rounds 3–4 decided —
 * Delete = contextual deletion, W/Shift+W wraps, drag-to-iterate, dbl-click
 * normalize, the context-filtered infer-first citation menu, folded
 * instantiation — producing ProofSteps through a sink instead of mutating
 * directly, so a proof SESSION can record them (round 5) and a free page can
 * apply them straight to the sheet.
 */
import type { NodeId, RegionId } from '../src/kernel/diagram/diagram'
import type { SubgraphSelection } from '../src/kernel/diagram/subgraph/selection'
import type { ProofStep, ProofContext } from '../src/kernel/proof/step'
import { applyConversion } from '../src/kernel/rules/conversion'
import { convertToHeadNormal, convertToWeakHeadNormal } from '../src/app/tactics'
import { inferFoldArgs } from '../src/app/define'
import { parseTerm } from '../src/kernel/term/parse'
import { polarity } from '../src/kernel/diagram/regions'
import { hitShapes, installBrush, promptAt, type BrushHandle, type LabCtx } from './shared'
import { discover, iterationTargets, FUEL } from './prove'
import { citeCandidates, citeFrom, citeOccurrences, emptySelAt, foldedComp, occToSel, occurrencesContaining } from './prove4'
import type { Occurrence } from '../src/kernel/diagram/subgraph/match'
import type { Vec2 } from '../src/view/vec'

export type MoveSink = {
  readonly ctx: ProofContext
  /** Apply a step. The sink owns routing: a forward track applies it as-is,
      a backward track applies it with the flipped-gate orientation and
      records the inverse (USER ruling: ONE vocabulary, shared execution). */
  apply(step: ProofStep): void
  refuse(text: string): void
  /** The active reasoning direction — flips exactly the polarity gates in
      discovery. Absent = forward. */
  mode?(): 'forward' | 'backward'
  /** Session pages own undo (session history, not the lab's); absent = lab undo. */
  undo?(): void
}

export function installVerdictMoves(lab: LabCtx, sink: MoveSink, opts: { active?: () => boolean } = {}): BrushHandle {
  const ctx = sink.ctx
  const act = opts.active ?? (() => true)
  const mode = () => sink.mode?.() ?? 'forward'
  const guarded = (fn: () => void): boolean => {
    try { fn(); return true } catch (e) { sink.refuse(e instanceof Error ? e.message : String(e)); return false }
  }
  let lastMouse = { sx: innerWidth / 2, sy: innerHeight / 2 }
  lab.canvas.addEventListener('pointermove', (e) => { lastMouse = { sx: e.clientX, sy: e.clientY } })

  // ---- right-click detection ----
  let rightDown: { sx: number; sy: number } | null = null
  let menu: HTMLDivElement | null = null
  const closeMenu = () => { menu?.remove(); menu = null }
  let iterDrag: { sel: SubgraphSelection; targets: RegionId[]; cursor: Vec2; over: RegionId | null } | null = null
  const brush = installBrush(lab, (h, e) => {
    if (e.button === 2) { rightDown = { sx: e.clientX, sy: e.clientY }; return true }
    if (e.button === 0 && h?.kind === 'node' && brush.isSelected(h)) {
      const disc = discover(lab, brush.selected, ctx, mode() === 'backward')
      if (disc === null || !disc.actions.some((a) => a.kind === 'iterate')) return false
      iterDrag = { sel: disc.sel, targets: iterationTargets(lab, disc.sel), cursor: lab.toWorld(e.clientX, e.clientY), over: null }
      return true
    }
    return false
  }, act)
  window.addEventListener('keydown', (e) => {
    if (!act()) return
    if (document.activeElement instanceof HTMLInputElement) return
    if (!(e.ctrlKey || e.metaKey) || e.key !== 'z') return
    e.preventDefault()
    if (sink.undo) { sink.undo(); brush.prune(); return }
    if (lab.undo()) { brush.prune(); lab.toast('undo') } else lab.toast('nothing to undo')
  })
  lab.canvas.addEventListener('contextmenu', (e) => e.preventDefault())
  lab.canvas.addEventListener('pointerdown', () => closeMenu())
  window.addEventListener('keydown', (e) => { if (e.key === 'Escape') closeMenu() })
  lab.canvas.addEventListener('pointerup', (e) => {
    if (!act()) { rightDown = null; iterDrag = null; return }
    if (rightDown !== null) {
      const rd = rightDown
      rightDown = null
      if (Math.hypot(e.clientX - rd.sx, e.clientY - rd.sy) <= 4) openMenu(rd)
      return
    }
    if (iterDrag !== null) {
      const it = iterDrag
      iterDrag = null
      if (it.over === null) { sink.refuse('release inside a glowing region to iterate'); return }
      if (guarded(() => sink.apply({ rule: 'iteration', sel: it.sel, target: it.over! }))) brush.clear()
    }
  })
  lab.canvas.addEventListener('pointermove', (e) => {
    if (!act() || iterDrag === null) return
    iterDrag.cursor = lab.toWorld(e.clientX, e.clientY)
    const r = lab.regionAt(iterDrag.cursor)
    iterDrag.over = iterDrag.targets.includes(r) ? r : null
  })
  lab.overlay((out) => {
    if (!act()) return
    if (iterDrag !== null) {
      for (const r of iterDrag.targets) {
        if (lab.d.regions[r]!.kind === 'sheet') continue
        const g = lab.engine.regions.get(r)
        if (g) out.push({ kind: 'circle', center: g.center, r: g.radius, fill: r === iterDrag.over ? '#16a34a22' : '#16a34a10', stroke: '#16a34a', width: r === iterDrag.over ? 2.4 : 1.4, insetColor: null, glow: null })
      }
    }
    if (cycle !== null) {
      const occ = cycle.occs[cycle.k]!
      for (const nid of occ.nodeMap.values()) out.push(...hitShapes(lab, { kind: 'node', id: nid }, '#7c3aed', 2.6))
      for (const wid of occ.wireMap.values()) out.push(...hitShapes(lab, { kind: 'wire', id: wid }, '#7c3aed', 2.6))
    }
  })

  // ---- dedicated keys (forward side only) ----
  window.addEventListener('keydown', (e) => {
    if (!act()) return
    if (document.activeElement instanceof HTMLInputElement) return
    if (e.key !== 'Delete' && e.key !== 'Backspace' && e.key !== 'w' && e.key !== 'W') return
    const disc = discover(lab, brush.selected, ctx, mode() === 'backward')
    if (disc === null) { sink.refuse(brush.selected.length === 0 ? 'select something first' : 'this selection spans several regions'); return }
    if (e.key === 'Delete' || e.key === 'Backspace') {
      const byKind = (k: string) => disc.actions.find((a) => a.kind === k)
      const a = byKind('doubleCutElim') ?? byKind('vacuousElim') ?? byKind('erase') ?? byKind('deiterate')
      if (a === undefined) { sink.refuse('nothing here reads as a deletion'); return }
      const step: ProofStep = a.kind === 'doubleCutElim' ? { rule: 'doubleCutElim', region: disc.sel.regions[0]! }
        : a.kind === 'vacuousElim' ? { rule: 'vacuousElim', region: disc.sel.regions[0]! }
        : a.kind === 'erase' ? { rule: 'erasure', sel: disc.sel }
        : { rule: 'deiteration', sel: disc.sel, fuel: FUEL }
      if (guarded(() => sink.apply(step))) brush.clear()
    } else if (e.shiftKey) {
      promptAt(innerWidth / 2 - 100, 60, 'bubble arity (e.g. 1)', (t) => {
        const n = Number(t)
        if (!Number.isInteger(n) || n < 0) { sink.refuse(`'${t}' is not a valid arity`); return false }
        if (guarded(() => sink.apply({ rule: 'vacuousIntro', sel: disc.sel, arity: n }))) { brush.clear(); return true }
        return false
      })
    } else if (guarded(() => sink.apply({ rule: 'doubleCutIntro', sel: disc.sel }))) brush.clear()
  })

  // ---- double-click a term = normalize ----
  const normalize = (node: NodeId): void => {
    const attempt = (fn: () => void): boolean => { try { fn(); return true } catch { return false } }
    if (attempt(() => sink.apply(convertToWeakHeadNormal(lab.d, node, FUEL).step))) { brush.clear(); return }
    if (attempt(() => sink.apply(convertToHeadNormal(lab.d, node, FUEL).step))) { brush.clear(); return }
    sink.refuse('already in normal form — use Convert → custom target for a specific βη-equal shape')
  }
  lab.canvas.addEventListener('dblclick', (e) => {
    if (!act()) return
    const h = lab.hitAt(e.clientX, e.clientY)
    if (h?.kind === 'node' && lab.d.nodes[h.id]!.kind === 'term') normalize(h.id)
  })

  // ---- occurrence cycling ----
  let cycle: { name: string; direction: 'forward' | 'reverse'; from: ReturnType<typeof citeFrom>; occs: Occurrence[]; k: number } | null = null
  const applyOcc = (): void => {
    const cy = cycle!
    const occ = cy.occs[cy.k]!
    const ok = guarded(() => {
      const at = { sel: occToSel(cy.from, occ, lab.d), args: [...occ.attachments] }
      sink.apply({ rule: 'theorem', name: cy.name, at, direction: cy.direction })
    })
    if (ok) { cycle = null; brush.clear() }
  }
  const beginCite = (c: { name: string; direction: 'forward' | 'reverse'; from: ReturnType<typeof citeFrom>; occs: Occurrence[] }): void => {
    cycle = { ...c, k: 0 }
    if (c.occs.length === 1) { applyOcc(); return }
    lab.toast(`${c.occs.length} occurrences of '${c.name}' — Tab/click cycles, Enter applies, Esc cancels`)
  }
  window.addEventListener('keydown', (e) => {
    if (!act() || cycle === null) return
    if (e.key === 'Escape') { cycle = null; lab.toast('citation cancelled') }
    else if (e.key === 'Tab') { e.preventDefault(); cycle.k = (cycle.k + 1) % cycle.occs.length; lab.toast(`occurrence ${cycle.k + 1}/${cycle.occs.length} — Enter applies`) }
    else if (e.key === 'Enter') applyOcc()
  })
  lab.canvas.addEventListener('pointerdown', (e) => {
    if (!act() || cycle === null || e.button !== 0 || e.ctrlKey) return
    e.stopImmediatePropagation()
    cycle.k = (cycle.k + 1) % cycle.occs.length
    lab.toast(`occurrence ${cycle.k + 1}/${cycle.occs.length} — Enter applies`)
  }, { capture: true })

  // ---- the context-filtered menu ----
  function openMenu(at: { sx: number; sy: number }): void {
    closeMenu()
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
    const backward = mode() === 'backward'
    const disc = discover(lab, brush.selected, ctx, backward)
    if (disc !== null) {
      for (const a of disc.actions) {
        if (a.kind === 'convert') {
          const node = disc.sel.nodes[0]!
          row('Normalize (also: double-click)', () => normalize(node))
          row('Convert → head normal', () => { if (guarded(() => sink.apply(convertToHeadNormal(lab.d, node, FUEL).step))) brush.clear() })
          row('Convert → custom target…', () => {
            promptAt(lastMouse.sx, lastMouse.sy, 'target term (βη-equal)', (t) =>
              guarded(() => {
                const conv = applyConversion(lab.d, node, parseTerm(t), FUEL)
                sink.apply({ rule: 'conversion', node, term: parseTerm(t), certificate: conv.certificate, attachments: {} })
                brush.clear()
              }))
          })
        } else if (a.kind === 'instantiate') {
          const bubble = disc.sel.regions[0]!
          for (const name of ctx.relations.keys()) {
            row(`Instantiate ${name}`, () => {
              if (guarded(() => sink.apply({ rule: 'comprehensionInstantiate', bubble, comp: foldedComp(ctx, name), attachments: [], binders: {} }))) brush.clear()
            })
          }
        } else if (a.kind === 'relUnfold') {
          row(a.label, () => { if (guarded(() => sink.apply({ rule: 'relUnfold', node: disc.sel.nodes[0]! }))) brush.clear() })
        } else if (a.kind === 'relFold') {
          row('Fold into…', () => {
            promptAt(lastMouse.sx, lastMouse.sy, `relation (${[...ctx.relations.keys()].join(', ')})`, (name) =>
              guarded(() => {
                const args = inferFoldArgs(lab.d, disc.sel, name.trim(), ctx)
                sink.apply({ rule: 'relFold', sel: disc.sel, defId: name.trim(), args })
                brush.clear()
              }))
          })
        }
      }
    }
    const pol = disc === null ? 'positive' : polarity(lab.d, disc.sel.region)
    const direction = (pol === 'positive') !== backward ? 'forward' as const : 'reverse' as const
    const cands = citeCandidates(lab, ctx, disc === null ? [] : brush.selected, direction)
    if (cands.applicable.length > 0) {
      row(disc === null ? 'applicable here' : 'applicable to the selection', null)
      for (const c of cands.applicable) {
        row(`${c.name}  (${c.occs!.length === 1 ? 'applies' : `${c.occs!.length} places`}, ${direction})`, () => beginCite({ name: c.name, direction: c.direction, from: c.from, occs: c.occs! }))
      }
    }
    row('insert (closed statements)', null)
    for (const c of cands.closed) {
      row(c.name, () => {
        if (guarded(() => sink.apply({ rule: 'theorem', name: c.name, at: { sel: emptySelAt(lab.d, lab.d.root), args: [] }, direction: c.direction }))) brush.clear()
      })
    }
    document.body.append(menu)
  }
  return brush
}

/** Refusal bubble anchored at the selection (round-4 verdict placement). */
export function mkRefusalBubble(lab: LabCtx, getBrush: () => BrushHandle | null): (text: string) => void {
  let lastMouse = { sx: innerWidth / 2, sy: innerHeight / 2 }
  lab.canvas.addEventListener('pointermove', (e) => { lastMouse = { sx: e.clientX, sy: e.clientY } })
  let timer: number | undefined
  return (text) => {
    document.getElementById('refusal-bubble')?.remove()
    const brush = getBrush()
    const at = (() => {
      if (brush === null) return lastMouse
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
    clearTimeout(timer)
    timer = window.setTimeout(() => el.remove(), 6000)
  }
}