/**
 * Round-4 machinery: parameterized proof moves against the REAL Frege theory
 * (verified relations + theorems). Discovery still comes from
 * applicableActions; commits run kernel appliers / proof steps; refusal copy
 * is the kernel's, placement is each variant page's question.
 */
import type { Diagram, NodeId, RegionId, WireId } from '../src/kernel/diagram/diagram'
import { DiagramBuilder } from '../src/kernel/diagram/builder'
import { parseTerm } from '../src/kernel/term/parse'
import { polarity } from '../src/kernel/diagram/regions'
import { mkSelection, type SubgraphSelection } from '../src/kernel/diagram/subgraph/selection'
import { findOccurrences, type Occurrence } from '../src/kernel/diagram/subgraph/match'
import { mkDiagramWithBoundary, type DiagramWithBoundary } from '../src/kernel/diagram/boundary'
import { applyStep, type ProofContext } from '../src/kernel/proof/step'
import { verifyTheory } from '../src/kernel/proof/store'
import { buildFregeTheory } from '../src/theories/frege'
import type { Hit } from '../src/app/hittest'
import type { BrushHandle, LabCtx } from './shared'
import { discover, FUEL } from './prove'

/** The real, verified Frege arithmetic theory (replay-is-verification). */
export function fregeCtx(): ProofContext {
  return verifyTheory(buildFregeTheory())
}

/** Citation-ready showcase: TWO copies of succNat's lhs shape
    (nat(n) ∧ Succ(n,s)) so inference meets a genuine ambiguity, a β-redex
    term for conversion, and a negatively-placed guard bubble for
    instantiation. */
export function showcase4(): { d: Diagram; boundary: WireId[] } {
  const b = new DiagramBuilder()
  for (let k = 0; k < 2; k++) {
    const n = b.ref(b.root, 'nat', 1)
    const s = b.ref(b.root, 'succ', 2)
    b.wire(b.root, [
      { node: n, port: { kind: 'arg', index: 0 } },
      { node: s, port: { kind: 'arg', index: 0 } },
    ])
    b.wire(b.root, [{ node: s, port: { kind: 'arg', index: 1 } }])
  }
  const t = b.termNode(b.root, parseTerm('(\\x. x x) (\\y. y)'))
  b.wire(b.root, [{ node: t, port: { kind: 'output' } }])
  const cut = b.cut(b.root)
  const bub = b.bubble(cut, 1)
  const a = b.atom(bub, bub)
  b.wire(bub, [{ node: a, port: { kind: 'arg', index: 0 } }])
  return { d: b.build(), boundary: [] }
}

/** The from-side a citation must match (forward: lhs, reverse: rhs). */
export function citeFrom(ctx: ProofContext, name: string, direction: 'forward' | 'reverse'): DiagramWithBoundary {
  const thm = ctx.theorems.get(name)
  if (thm === undefined) throw new Error(`unknown theorem '${name}'`)
  return direction === 'forward' ? thm.lhs : thm.rhs
}

/** A closed statement cites as an empty-selection insertion: args are []. */
export function citeIsClosed(from: DiagramWithBoundary): boolean {
  return from.boundary.length === 0
    && Object.keys(from.diagram.nodes).length === 0
    && Object.keys(from.diagram.wires).length === 0
}

export function emptySelAt(d: Diagram, region: RegionId): SubgraphSelection {
  return mkSelection(d, { region, regions: [], nodes: [], wires: [] })
}

export { occurrenceSelection as occToSel } from '../src/kernel/diagram/subgraph/match'

/** Every occurrence of the citation's from-side in the current diagram —
    the infer-first flow's search (exact mode: the matcher's default UX law). */
export function citeOccurrences(lab: LabCtx, from: DiagramWithBoundary): Occurrence[] {
  return [...findOccurrences(lab.d, from, { fuel: FUEL, mode: 'exact' }).matches]
}

/** Selection disambiguates (USER ruling): keep only occurrences whose image
    CONTAINS every selected item. Whether the user brushed the wires along
    with the nodes must not matter — the matcher derives the real seam. */
export function occurrencesContaining(occs: readonly Occurrence[], hits: readonly Hit[]): Occurrence[] {
  return occs.filter((occ) => {
    const nodeImg = new Set(occ.nodeMap.values())
    const wireImg = new Set(occ.wireMap.values())
    const regionImg = new Set(occ.regionMap.values())
    return hits.every((h) =>
      h.kind === 'node' ? nodeImg.has(h.id)
      : h.kind === 'wire' ? wireImg.has(h.id)
      : regionImg.has(h.id))
  })
}

export type CiteCandidate = {
  readonly name: string
  readonly direction: 'forward' | 'reverse'
  readonly from: DiagramWithBoundary
  /** null = closed statement (insertion, always available). */
  readonly occs: Occurrence[] | null
}

/** The context-filtered theorem list (USER ruling: never show a theorem that
    cannot apply HERE; a selection narrows to occurrences containing it).
    Closed statements are always insertable and listed separately. */
export function citeCandidates(lab: LabCtx, ctx: ProofContext, hits: readonly Hit[], direction: 'forward' | 'reverse'): { applicable: CiteCandidate[]; closed: CiteCandidate[] } {
  const applicable: CiteCandidate[] = []
  const closed: CiteCandidate[] = []
  for (const [name] of ctx.theorems) {
    const from = citeFrom(ctx, name, direction)
    if (citeIsClosed(from)) { closed.push({ name, direction, from, occs: null }); continue }
    const occs = occurrencesContaining(citeOccurrences(lab, from), hits)
    if (occs.length > 0) applicable.push({ name, direction, from, occs })
  }
  return { applicable, closed }
}

/** A comprehension that stays FOLDED (USER ruling): instantiating a named
    relation splices its REF NODE, never its body — unfold is a later,
    selective choice. */
export function foldedComp(ctx: ProofContext, name: string): DiagramWithBoundary {
  const body = ctx.relations.get(name)
  if (body === undefined) throw new Error(`unknown relation '${name}'`)
  const arity = body.boundary.length
  const b = new DiagramBuilder()
  const r = b.ref(b.root, name, arity)
  const ws: WireId[] = []
  for (let i = 0; i < arity; i++) ws.push(b.wire(b.root, [{ node: r, port: { kind: 'arg', index: i } }]))
  return mkDiagramWithBoundary(b.build(), ws)
}

export function applyCitation(lab: LabCtx, ctx: ProofContext, name: string, direction: 'forward' | 'reverse', sel: SubgraphSelection, args: readonly WireId[]): Diagram {
  return applyStep(lab.d, { rule: 'theorem', name, at: { sel, args: [...args] }, direction }, ctx)
}

export type ParamPick =
  | { kind: 'convert'; node: NodeId; sel: SubgraphSelection }
  | { kind: 'instantiate'; bubble: RegionId; sel: SubgraphSelection }
  | { kind: 'fold'; sel: SubgraphSelection }
  | { kind: 'cite'; name: string; direction: 'forward' | 'reverse'; sel: SubgraphSelection | null }

let menu: HTMLDivElement | null = null
export function closeMoveMenu(): void { menu?.remove(); menu = null }

/** The round-4 move menu at a point (pages open it from the decided trigger,
    a still right-click): the PARAMETERIZED moves for the selection, plus the
    theorem list. Zero-param unfold commits immediately. `citeBare`
    (infer-first pages) lists theorems even with nothing selected. */
export function openMoveMenu(lab: LabCtx, brush: BrushHandle, ctx: ProofContext, at: { sx: number; sy: number }, onPick: (p: ParamPick) => void, opts: { citeBare?: boolean; onRefuse: (text: string) => void }): void {
  closeMoveMenu()
  const disc = discover(lab, brush.selected, ctx)
  if (disc === null && !opts.citeBare) {
    opts.onRefuse(brush.selected.length === 0 ? 'select something first — the menu lists ITS moves' : 'this selection spans several regions')
    return
  }
  menu = document.createElement('div')
  menu.style.cssText = `position:fixed;left:${Math.min(at.sx, innerWidth - 280)}px;top:${Math.min(at.sy, innerHeight - 380)}px;z-index:8;width:260px;background:#fff;border:1.5px solid #d97706;border-radius:8px;box-shadow:0 4px 16px #0003;font:13px system-ui;max-height:360px;overflow-y:auto`
  const row = (label: string, onClick: (() => void) | null): void => {
    const r = document.createElement('div')
    r.textContent = label
    r.style.cssText = `padding:6px 10px;${onClick ? 'cursor:pointer' : 'color:#999;font-size:11px;text-transform:uppercase;border-top:1px solid #eee'}`
    if (onClick) {
      r.addEventListener('pointerenter', () => { r.style.background = '#fde68a55' })
      r.addEventListener('pointerleave', () => { r.style.background = '' })
      r.addEventListener('click', () => { closeMoveMenu(); onClick() })
    }
    menu!.append(r)
  }
  if (disc !== null) {
    for (const a of disc.actions) {
      if (a.kind === 'convert') row(a.label, () => onPick({ kind: 'convert', node: disc.sel.nodes[0]!, sel: disc.sel }))
      else if (a.kind === 'instantiate') row(a.label, () => onPick({ kind: 'instantiate', bubble: disc.sel.regions[0]!, sel: disc.sel }))
      else if (a.kind === 'relFold') row(a.label, () => onPick({ kind: 'fold', sel: disc.sel }))
      else if (a.kind === 'relUnfold') row(a.label, () => {
        guardedCommit(lab, opts.onRefuse, () => {
          lab.mutate(applyStep(lab.d, { rule: 'relUnfold', node: disc.sel.nodes[0]! }, ctx))
          brush.clear()
        })
      })
    }
  }
  row('cite a theorem', null)
  const pol = disc === null ? 'positive' : polarity(lab.d, disc.sel.region)
  const direction = pol === 'positive' ? 'forward' as const : 'reverse' as const
  for (const [name] of ctx.theorems) {
    const from = citeFrom(ctx, name, direction)
    row(`${name}  ${citeIsClosed(from) ? '(closed)' : `(${from.boundary.length} args, ${direction})`}`,
      () => onPick({ kind: 'cite', name, direction, sel: disc?.sel ?? null }))
  }
  document.body.append(menu)
}

/** Page-facing guarded commit with variant-owned refusal placement. */
export function guardedCommit(lab: LabCtx, onRefuse: (t: string) => void, fn: () => void): boolean {
  try { fn(); return true } catch (e) { onRefuse(e instanceof Error ? e.message : String(e)); return false }
}

/** Right-click detection shared by the round-4 pages: claim on button 2,
    open the menu on a still release. Returns the brush claim callback. */
export function rightClickMenu(lab: LabCtx, getBrush: () => BrushHandle, ctx: ProofContext, onPick: (p: ParamPick) => void, opts: { citeBare?: boolean; onRefuse: (text: string) => void }): (h: Hit | null, e: PointerEvent) => boolean {
  let rightDown: { sx: number; sy: number } | null = null
  lab.canvas.addEventListener('contextmenu', (e) => e.preventDefault())
  window.addEventListener('keydown', (e) => { if (e.key === 'Escape') closeMoveMenu() })
  lab.canvas.addEventListener('pointerdown', () => closeMoveMenu())
  lab.canvas.addEventListener('pointerup', (e) => {
    if (rightDown === null) return
    const rd = rightDown
    rightDown = null
    if (Math.hypot(e.clientX - rd.sx, e.clientY - rd.sy) > 4) return
    openMoveMenu(lab, getBrush(), ctx, rd, onPick, opts)
  })
  return (_h, e) => {
    if (e.button !== 2) return false
    rightDown = { sx: e.clientX, sy: e.clientY }
    return true
  }
}
