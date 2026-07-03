/**
 * Round-3 machinery: PROVE-mode labs. Discovery comes from the app's own
 * `applicableActions` (mirrored gates); commits call the kernel appliers, and
 * every refusal message reaches the toast verbatim (the law: kernel copy IS
 * the UX copy). No construction gestures here — rules are the only moves.
 */
import { parseTerm } from '../src/kernel/term/parse'
import { DiagramBuilder } from '../src/kernel/diagram/builder'
import type { Diagram, RegionId, WireId } from '../src/kernel/diagram/diagram'
import { isAncestorOrEqual } from '../src/kernel/diagram/regions'
import type { SubgraphSelection } from '../src/kernel/diagram/subgraph/selection'
import type { ProofContext } from '../src/kernel/proof/step'
import { applicableActions, type ActionDescriptor } from '../src/app/actions'
import { buildSelection, type Hit } from '../src/app/hittest'
import { applyErasure } from '../src/kernel/rules/erasure'
import { applyDoubleCutIntro, applyDoubleCutElim } from '../src/kernel/rules/doublecut'
import { applyVacuousBubbleIntro, applyVacuousBubbleElim } from '../src/kernel/rules/vacuous'
import { applyIteration, applyDeiteration } from '../src/kernel/rules/iteration'
import { mkEngine } from '../src/view/engine'
import { settleStep } from '../src/view/relax'
import { paint, LIGHT, type Shape } from '../src/view/paint'
import { drawShapes } from '../src/view/canvas'
import { promptAt, tryEdit, type BrushHandle, type LabCtx } from './shared'

export const PROVE_CTX: ProofContext = { theorems: new Map(), relations: new Map() }

/** The app's fuel default (shell's fuel input starts at 64). */
export const FUEL = 64

/** Polarity-rich showcase: erasable content in positive depth, a deiterable
    copy in a negative cut, a clean double cut, a vacuous bubble. */
export function proveShowcase(): { d: Diagram; boundary: WireId[] } {
  const b = new DiagramBuilder()
  const p = (s: string) => parseTerm(s)
  const tA = b.termNode(b.root, p('f g'))
  b.wire(b.root, [{ node: tA, port: { kind: 'output' } }])
  b.wire(b.root, [{ node: tA, port: { kind: 'freeVar', name: 'f' } }])
  b.wire(b.root, [{ node: tA, port: { kind: 'freeVar', name: 'g' } }])
  const tB = b.termNode(b.root, p('\\x. x'))
  b.wire(b.root, [{ node: tB, port: { kind: 'output' } }])
  const cut1 = b.cut(b.root)
  const tB2 = b.termNode(cut1, p('\\x. x'))
  b.wire(cut1, [{ node: tB2, port: { kind: 'output' } }])
  const cut2 = b.cut(cut1)
  const tC = b.termNode(cut2, p('\\y. y y'))
  b.wire(cut2, [{ node: tC, port: { kind: 'output' } }])
  const cutD = b.cut(b.root)
  const cutE = b.cut(cutD)
  const tD = b.termNode(cutE, p('\\z. z'))
  b.wire(cutE, [{ node: tD, port: { kind: 'output' } }])
  b.bubble(b.root, 1)
  return { d: b.build(), boundary: [] }
}

/** Applicable actions for the current brush selection (empty list when the
    hits do not form a kernel selection). */
export function discover(lab: LabCtx, hits: readonly Hit[]): { sel: SubgraphSelection; actions: ActionDescriptor[] } | null {
  if (hits.length === 0) return null
  try {
    const sel = buildSelection(lab.d, hits)
    return { sel, actions: applicableActions(lab.d, sel, PROVE_CTX) }
  } catch {
    return null
  }
}

/** Static explanations for why a rule is dim (variant B's teaching layer). */
export const RULE_VOCAB: { kind: ActionDescriptor['kind']; label: string; why: string }[] = [
  { kind: 'erase', label: 'Erase', why: 'needs a selection in a POSITIVE region' },
  { kind: 'insert', label: 'Insert…', why: 'needs an EMPTY selection spot in a NEGATIVE region (parameterized — round 4)' },
  { kind: 'doubleCutWrap', label: 'Double-cut wrap', why: 'needs a selection' },
  { kind: 'doubleCutElim', label: 'Double-cut elim', why: 'needs ONE selected cut whose only content is another cut' },
  { kind: 'vacuousWrap', label: 'Vacuous bubble wrap…', why: 'needs a selection' },
  { kind: 'vacuousElim', label: 'Dissolve vacuous bubble', why: 'needs ONE selected bubble binding no atoms' },
  { kind: 'iterate', label: 'Iterate into…', why: 'needs a selection (copies it into a region within its scope)' },
  { kind: 'deiterate', label: 'Deiterate', why: 'needs a selection justified by an identical copy in scope' },
  { kind: 'convert', label: 'Convert (βη)…', why: 'needs ONE selected λ-term node (parameterized — round 4)' },
]

/** Regions a selection may iterate into (mirror; the kernel is the authority). */
export function iterationTargets(lab: LabCtx, sel: SubgraphSelection): RegionId[] {
  const inSelection = (r: RegionId): boolean => {
    let cur = r
    for (;;) {
      if (sel.regions.includes(cur)) return true
      const reg = lab.d.regions[cur]!
      if (reg.kind === 'sheet') return false
      cur = reg.parent
    }
  }
  return Object.keys(lab.d.regions).filter((r) => isAncestorOrEqual(lab.d, sel.region, r) && !inSelection(r))
}

/** Commit a discovered action. Returns true when the diagram changed.
    `pickTarget` drives the iterate second phase; parameterized kinds
    (insert/convert) are refused with a pointer to their round. */
export function commit(lab: LabCtx, brush: BrushHandle, sel: SubgraphSelection, a: ActionDescriptor, target?: RegionId): boolean {
  const done = (make: () => Diagram, note: string): boolean => {
    const ok = tryEdit(lab, () => { lab.mutate(make()) })
    if (ok) { brush.clear(); lab.toast(note) }
    return ok
  }
  switch (a.kind) {
    case 'erase': return done(() => applyErasure(lab.d, sel), 'erased (positive region)')
    case 'doubleCutWrap': return done(() => applyDoubleCutIntro(lab.d, sel), 'wrapped in a double cut')
    case 'doubleCutElim': return done(() => applyDoubleCutElim(lab.d, sel.regions[0]!), 'double cut eliminated')
    case 'vacuousElim': return done(() => applyVacuousBubbleElim(lab.d, sel.regions[0]!), 'vacuous bubble dissolved')
    case 'deiterate': return done(() => applyDeiteration(lab.d, sel, FUEL), 'deiterated against its justifying copy')
    case 'iterate':
      if (target === undefined) { lab.toast('iterate: pick a target region'); return false }
      return done(() => applyIteration(lab.d, sel, target), `iterated into '${target}'`)
    case 'vacuousWrap':
      promptAt(innerWidth / 2 - 100, 60, 'bubble arity (e.g. 1)', (t) => {
        const n = Number(t)
        if (!Number.isInteger(n) || n < 0) { lab.toast(`'${t}' is not a valid arity`); return false }
        return done(() => applyVacuousBubbleIntro(lab.d, sel, n), 'wrapped in a vacuous bubble')
      })
      return false
    case 'insert': case 'convert': case 'instantiate': case 'relUnfold': case 'relFold': case 'citeTheorem':
      lab.toast(`${a.label} is parameterized — its flow is round 4's question`)
      return false
  }
}

/** Try an action headlessly (for result previews): the diagram it would
    produce, or null when the kernel refuses or the kind is parameterized. */
export function tryAction(lab: LabCtx, sel: SubgraphSelection, a: ActionDescriptor, target?: RegionId): Diagram | null {
  try {
    switch (a.kind) {
      case 'erase': return applyErasure(lab.d, sel)
      case 'doubleCutWrap': return applyDoubleCutIntro(lab.d, sel)
      case 'doubleCutElim': return applyDoubleCutElim(lab.d, sel.regions[0]!)
      case 'vacuousElim': return applyVacuousBubbleElim(lab.d, sel.regions[0]!)
      case 'deiterate': return applyDeiteration(lab.d, sel, FUEL)
      case 'iterate': return target === undefined ? null : applyIteration(lab.d, sel, target)
      default: return null
    }
  } catch {
    return null
  }
}

/** Render a diagram into an inset canvas (the ghost preview): fresh engine,
    synchronous settle, fit, paint — the real pipeline, miniaturized. */
export function renderPreview(canvas: HTMLCanvasElement, d: Diagram, boundary: readonly WireId[]): void {
  const eng = mkEngine(d, boundary as WireId[])
  for (let i = 0; i < 240; i++) settleStep(eng)
  const sheet = eng.regions.get(d.root)
  const R = Math.max(sheet?.radius ?? 10, 10)
  const cx = sheet?.center.x ?? 0, cy = sheet?.center.y ?? 0
  const scale = (0.44 * Math.min(canvas.width, canvas.height)) / R
  const view = { scale, offsetX: canvas.width / 2 - cx * scale, offsetY: canvas.height / 2 - cy * scale }
  const shapes: Shape[] = [...paint(eng, LIGHT)]
  const g = canvas.getContext('2d')!
  g.clearRect(0, 0, canvas.width, canvas.height)
  drawShapes(g, shapes, view)
}

/** The iterate second phase: legal targets glow green; clicking one commits;
    Esc (or any other button) cancels. Shared by every Round-3 variant. */
export function installTargetPhase(lab: LabCtx, brush: BrushHandle): { begin(sel: SubgraphSelection, a: ActionDescriptor): void; active(): boolean } {
  let st: { sel: SubgraphSelection; a: ActionDescriptor; targets: RegionId[] } | null = null
  window.addEventListener('keydown', (e) => { if (e.key === 'Escape') st = null })
  lab.canvas.addEventListener('pointerdown', (e) => {
    if (st === null) return
    e.stopImmediatePropagation()
    const cur = st
    st = null
    if (e.button !== 0) return
    const r = lab.regionAt(lab.toWorld(e.clientX, e.clientY))
    if (!cur.targets.includes(r)) { lab.toast('that region is not a legal target for this iteration'); return }
    commit(lab, brush, cur.sel, cur.a, r)
  }, { capture: true })
  lab.overlay((out) => {
    if (st === null) return
    for (const r of st.targets) {
      if (lab.d.regions[r]!.kind === 'sheet') continue
      const g = lab.engine.regions.get(r)
      if (g) out.push({ kind: 'circle', center: g.center, r: g.radius, fill: '#16a34a12', stroke: '#16a34a', width: 1.6, insetColor: null, glow: null })
    }
  })
  return {
    begin: (sel, a) => {
      st = { sel, a, targets: iterationTargets(lab, sel) }
      lab.toast('iterate: click a green region — the sheet itself counts too (Esc cancels)')
    },
    active: () => st !== null,
  }
}

export function installUndoKey(lab: LabCtx, brush: BrushHandle): void {
  window.addEventListener('keydown', (e) => {
    if (document.activeElement instanceof HTMLInputElement) return
    if ((e.ctrlKey || e.metaKey) && e.key === 'z') {
      e.preventDefault()
      if (lab.undo()) { brush.prune(); lab.toast('undo') } else lab.toast('nothing to undo')
    }
  })
}
