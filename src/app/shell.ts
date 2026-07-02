import type { Diagram, Endpoint, NodeId, RegionId, WireId } from '../kernel/diagram/diagram'
import type { DiagramWithBoundary } from '../kernel/diagram/boundary'
import { mkDiagramWithBoundary } from '../kernel/diagram/boundary'
import type { Term } from '../kernel/term/term'
import { parseTerm } from '../kernel/term/parse'
import type { SubgraphSelection } from '../kernel/diagram/subgraph/selection'
import { polarity } from '../kernel/diagram/regions'
import { applyConversion } from '../kernel/rules/conversion'
import type { ProofContext, ProofStep } from '../kernel/proof/step'
import { checkTheorem } from '../kernel/proof/theorem'
import type { Vec2 } from '../view/vec'
import { vec, length, sub } from '../view/vec'
import type { Engine } from '../view/engine'
import { mkEngine } from '../view/engine'
import { settleStep } from '../view/relax'
import { legPaths, boundaryExits, existentialStubs } from '../view/wires'
import type { Shape, Theme } from '../view/paint'
import { paint, LIGHT } from '../view/paint'
import { drawShapes } from '../view/canvas'
import { bootBundledContext } from './boot'
import { emptyDiagram, addTermNode, addCut, addBubble, joinPorts, deleteSelection } from './edit'
import type { ProofSession } from './session'
import { startSession, applyForward, applyBackward, undoForward, undoBackward, meet, assembleTheorem, adoptTheorem } from './session'
import { sessionTheory } from './persist'
import { loadTheory, theoryToJson } from '../kernel/proof/store'
import type { Hit } from './hittest'
import { hitTest, buildSelection } from './hittest'
import type { ActionDescriptor } from './actions'
import { applicableActions } from './actions'

/**
 * The DOM shell: browser glue over the tested headless core (edit, session,
 * hittest, actions) and the view layer. Every decision branch here calls a
 * tested function; the shell itself owns only browser concerns — mode state,
 * the displayed diagram, selection, pending two-phase actions, physics
 * seeding + pin-while-drag, the viewport transform, and chrome wiring.
 * Behavioral coverage is Plan 10d's E2E.
 */

export type ShellOptions = {
  readonly canvas: HTMLCanvasElement
  readonly chrome: HTMLElement
}

/**
 * UI input tolerances, CSS pixels. Like WIRE_TOLERANCE these are documented
 * interaction constants, not correctness heuristics: pointer coordinates
 * quantize to whole pixels and hands tremble 1–2px during a click, so a
 * zero movement threshold would misclassify ordinary clicks as drags; wheel
 * deltas arrive in pixel units and map exponentially to zoom so equal wheel
 * travel gives equal zoom RATIO at any scale.
 */
const CLICK_SLOP_PX = 3
const ZOOM_PER_WHEEL_PX = 0.001

/** Relaxation ticks advanced per animation frame (visual pacing only). */
const SETTLE_STEPS_PER_FRAME = 4

const SELECT_STROKE = '#d97706'
const HOVER_STROKE = '#2563eb'

type Pending =
  | { readonly kind: 'iterate'; readonly sel: SubgraphSelection }
  | { readonly kind: 'cite'; readonly name: string; readonly direction: 'forward' | 'reverse'; readonly sel: SubgraphSelection; readonly args: WireId[] }
  | { readonly kind: 'unCite'; readonly name: string; readonly sel: SubgraphSelection; readonly args: WireId[] }
  | { readonly kind: 'relFold'; readonly defId: string; readonly sel: SubgraphSelection; readonly args: WireId[] }

type Drag =
  | { readonly kind: 'node'; readonly node: NodeId }
  | { readonly kind: 'pan'; readonly startOffset: { readonly x: number; readonly y: number }; readonly startScreen: Vec2 }

/**
 * Backward menu entry: a labelled action that commits at button-click time,
 * reading term/fuel from the live inputs. needsInput flags are advisory only —
 * the commit lambda reads the inputs directly when the button is clicked.
 */
type BackwardEntry =
  | { readonly kind: 'unDoubleCut'; readonly label: string; readonly outer: RegionId }
  | { readonly kind: 'unVacuousBubble'; readonly label: string; readonly bubble: RegionId }
  | { readonly kind: 'unErase'; readonly label: string; readonly region: RegionId; readonly needsInput: 'pattern' }
  | { readonly kind: 'unConvert'; readonly label: string; readonly node: NodeId; readonly needsInput: 'term' }
  | { readonly kind: 'unCite'; readonly label: string; readonly name: string; readonly sel: SubgraphSelection }

/**
 * Enumerate the backward moves the UI offers for a selection. Commit-time
 * input reading means the entries do NOT depend on the current term/fuel
 * input values — they describe what the button will do when clicked.
 */
function backwardEntries(d: Diagram, sel: SubgraphSelection, ctx: ProofContext): BackwardEntry[] {
  const out: BackwardEntry[] = []
  // doubleCutElim → unDoubleCut: exactly one selected region, must be an outer cut of a double-cut pair
  if (sel.regions.length === 1 && sel.nodes.length === 0 && sel.wires.length === 0) {
    const rid = sel.regions[0]!
    const r = d.regions[rid]
    if (r !== undefined && r.kind === 'cut') {
      const children = Object.entries(d.regions).filter(([, x]) => x.kind !== 'sheet' && x.parent === rid)
      const nodesIn = Object.values(d.nodes).some((n) => n.region === rid)
      const wiresIn = Object.values(d.wires).some((w) => w.scope === rid)
      if (children.length === 1 && children[0]![1].kind === 'cut' && !nodesIn && !wiresIn) {
        out.push({ kind: 'unDoubleCut', label: 'Un-wrap double cut (backward)', outer: rid })
      }
    }
    if (r !== undefined && r.kind === 'bubble') {
      const bound = Object.values(d.nodes).some((n) => n.kind === 'atom' && n.binder === rid)
      if (!bound) {
        out.push({ kind: 'unVacuousBubble', label: 'Dissolve vacuous bubble (backward)', bubble: rid })
      }
    }
  }
  // unErase: selected region is positive — at commit time the term input provides the pattern
  if (polarity(d, sel.region) === 'positive') {
    out.push({ kind: 'unErase', label: 'Un-erase into region (term input → pattern)…', region: sel.region, needsInput: 'pattern' })
  }
  // unConvert: single term node selected — at commit time term input + fuel provide the target
  if (sel.nodes.length === 1 && sel.regions.length === 0 && d.nodes[sel.nodes[0]!]?.kind === 'term') {
    out.push({ kind: 'unConvert', label: 'Un-convert node (term input + fuel)…', node: sel.nodes[0]!, needsInput: 'term' })
  }
  // unCite <name>: per theorem, at positive selections
  if (polarity(d, sel.region) === 'positive') {
    for (const [name] of ctx.theorems) {
      out.push({ kind: 'unCite', label: `Un-cite ${name} (backward)`, name, sel })
    }
  }
  return out
}

export function mountShell(opts: ShellOptions): { dispose(): void } {
  const { canvas, chrome } = opts
  const ctx2d = canvas.getContext('2d')
  if (ctx2d === null) throw new Error('the canvas has no 2d context')

  // ---- boot: both bundled theories through the verifying JSON road ----
  const boot = bootBundledContext()
  let ctx: ProofContext = boot.ctx
  let relations: Readonly<Record<string, DiagramWithBoundary>> = boot.relations
  let constNames: ReadonlySet<string> = boot.constNames

  // ---- state ----
  let mode: 'edit' | 'prove' = 'edit'
  let side: 'forward' | 'backward' = 'forward'
  let editDiagram = emptyDiagram()
  const editHistory: Diagram[] = []
  let goalLhs: DiagramWithBoundary | null = null
  let goalRhs: DiagramWithBoundary | null = null
  let session: ProofSession | null = null
  let hits: Hit[] = []
  let kernelSel: SubgraphSelection | null = null
  let pending: Pending | null = null
  // The render engine is rebuilt whenever the displayed diagram identity
  // changes (layout never persists). Boundary wiring for proof sides is Task 2;
  // an edit sheet has no boundary, so [] is correct here.
  let theme: Theme = LIGHT
  let displayed: Diagram = editDiagram
  let engine: Engine = mkEngine(displayed, [])
  settleStep(engine)
  let pin: { readonly node: NodeId; pos: Vec2 } | null = null
  let message = 'EDIT mode: type a term (\\ is λ) and Add, click to select, wrap/delete/join'
  let drag: Drag | null = null
  let downScreen: Vec2 | null = null
  let dragMoved = false
  let hoverWorld: Vec2 | null = null
  let disposed = false
  let raf = 0

  canvas.width = window.innerWidth
  canvas.height = window.innerHeight
  canvas.style.background = theme.canvas
  const view = { scale: 6, offsetX: canvas.width / 2, offsetY: canvas.height / 2 }

  const toWorld = (screen: Vec2): Vec2 =>
    vec((screen.x - view.offsetX) / view.scale, (screen.y - view.offsetY) / view.scale)

  const currentDiagram = (): Diagram => {
    if (mode === 'prove' && session !== null) {
      return side === 'forward' ? session.forward.current : session.backward.current
    }
    return editDiagram
  }

  // ---- chrome ----
  const div = (cls: string): HTMLDivElement => {
    const d = document.createElement('div')
    d.className = cls
    return d
  }
  const button = (label: string, onClick: () => void): HTMLButtonElement => {
    const b = document.createElement('button')
    b.textContent = label
    b.type = 'button'
    b.addEventListener('click', onClick)
    return b
  }
  const textInput = (id: string, placeholder: string): HTMLInputElement => {
    const i = document.createElement('input')
    i.type = 'text'
    i.id = id
    i.placeholder = placeholder
    return i
  }
  const numberInput = (id: string, label: string, value: number): { wrap: HTMLElement; input: HTMLInputElement } => {
    const wrap = document.createElement('label')
    wrap.append(`${label} `)
    const input = document.createElement('input')
    input.type = 'number'
    input.id = id
    input.value = String(value)
    input.style.width = '4em'
    wrap.append(input)
    return { wrap, input }
  }

  const statusDiv = div('vpa-status')
  statusDiv.id = 'status'
  const editRow = div('vpa-row')
  const goalRow = div('vpa-row')
  const proveRow = div('vpa-row')
  const menuDiv = div('vpa-menu')
  menuDiv.id = 'action-menu'
  const theoremsDiv = div('vpa-theorems')
  theoremsDiv.id = 'theorems'

  // ---- context rebinding ----
  // Renders the theorem/relation/constant list from the live bindings.
  const renderTheoremList = (): void => {
    const thmNames = [...ctx.theorems.keys()]
    const relNames = Object.keys(relations)
    theoremsDiv.textContent =
      `theorems: ${thmNames.join(', ') || 'none'} · relations: ${relNames.join(', ') || 'none'} · constants: ${[...constNames].join(', ')}`
  }

  // Called after adopt and after load; refreshes all three context bindings and
  // re-renders the theorem list so the UI always reflects the live context.
  const setContext = (newCtx: ProofContext, newRelations: Readonly<Record<string, DiagramWithBoundary>>, newConstNames: ReadonlySet<string>): void => {
    ctx = newCtx
    relations = newRelations
    constNames = newConstNames
    renderTheoremList()
  }

  const termInput = textInput('term-input', 'term, e.g. \\x. x y (also: insertion pattern / convert target / relation name)')
  const nameInput = textInput('theorem-name', 'theorem name')
  const arity = numberInput('arity-input', 'arity', 1)
  const fuel = numberInput('fuel-input', 'fuel', 64)

  const guard = (fn: () => void) => (): void => {
    try {
      fn()
    } catch (e) {
      // the kernel's refusal message IS the UX copy — verbatim into the status line
      message = e instanceof Error ? e.message : String(e)
      refreshChrome()
    }
  }

  const readCount = (input: HTMLInputElement, what: string): number => {
    const n = Number(input.value)
    if (!Number.isInteger(n) || n < 1) throw new Error(`${what} must be a positive integer, got '${input.value}'`)
    return n
  }
  const parseInput = (): Term => {
    if (termInput.value.trim() === '') throw new Error('the term input is empty: type a term first (\\ is λ)')
    return parseTerm(termInput.value, constNames)
  }

  const sync = (): void => {
    const d = currentDiagram()
    if (d !== displayed) {
      // diagram identity changed: rebuild the engine (layout never persists),
      // drop selection/pending/pin — their ids belong to the old diagram
      displayed = d
      engine = mkEngine(d, [])
      settleStep(engine)
      pin = null
      hits = []
      kernelSel = null
      pending = null
    }
    refreshChrome()
  }

  const setHits = (next: Hit[]): void => {
    hits = next
    if (hits.length === 0) {
      kernelSel = null
    } else {
      try {
        kernelSel = buildSelection(displayed, hits)
        message = `selected ${hits.map((h) => `${h.kind} '${h.id}'`).join(', ')}`
      } catch (e) {
        kernelSel = null
        message = e instanceof Error ? e.message : String(e)
      }
    }
    refreshChrome()
  }

  // ---- edit operations (mkDiagram-validated surgery via edit.ts) ----
  const pushEdit = (d: Diagram): void => {
    editHistory.push(editDiagram)
    editDiagram = d
    sync()
  }
  const requireEdit = (): void => {
    if (mode !== 'edit') throw new Error('construction is an EDIT-mode operation; switch modes first')
  }
  const requireSel = (): SubgraphSelection => {
    if (kernelSel === null) throw new Error('no valid selection: click nodes/regions/wires of one region first')
    return kernelSel
  }

  const onAddTerm = guard(() => {
    requireEdit()
    const region = hits.length === 1 && hits[0]!.kind === 'region' ? hits[0]!.id : editDiagram.root
    const { diagram, node } = addTermNode(editDiagram, region, parseInput())
    pushEdit(diagram)
    message = `added term node '${node}' in region '${region}'`
    refreshChrome()
  })
  const onWrapCut = guard(() => {
    requireEdit()
    const { diagram, region } = addCut(editDiagram, requireSel())
    pushEdit(diagram)
    message = `wrapped selection in cut '${region}'`
    refreshChrome()
  })
  const onWrapBubble = guard(() => {
    requireEdit()
    const { diagram, region } = addBubble(editDiagram, requireSel(), readCount(arity.input, 'bubble arity'))
    pushEdit(diagram)
    message = `wrapped selection in bubble '${region}'`
    refreshChrome()
  })
  const onDelete = guard(() => {
    requireEdit()
    pushEdit(deleteSelection(editDiagram, requireSel()))
    message = 'deleted the selection'
    refreshChrome()
  })
  const onJoinWires = guard(() => {
    requireEdit()
    const wires = hits.filter((h): h is Hit & { kind: 'wire' } => h.kind === 'wire')
    if (wires.length !== 2) throw new Error(`joining needs exactly two selected wires, got ${wires.length}`)
    const repr = (id: WireId): Endpoint => {
      const w = editDiagram.wires[id]
      if (w === undefined) throw new Error(`unknown wire '${id}'`)
      const ep = w.endpoints[0]
      if (ep === undefined) throw new Error(`wire '${id}' has no endpoints to join through`)
      return ep
    }
    pushEdit(joinPorts(editDiagram, repr(wires[0]!.id), repr(wires[1]!.id)))
    message = `joined wires '${wires[0]!.id}' and '${wires[1]!.id}'`
    refreshChrome()
  })

  // ---- goal + session ----
  const onSetLhs = guard(() => {
    requireEdit()
    goalLhs = mkDiagramWithBoundary(editDiagram, [])
    session = null
    message = 'goal LHS snapshotted from the sheet'
    refreshChrome()
  })
  const onSetRhs = guard(() => {
    requireEdit()
    goalRhs = mkDiagramWithBoundary(editDiagram, [])
    session = null
    message = 'goal RHS snapshotted from the sheet'
    refreshChrome()
  })

  const meetStatus = (): string => {
    if (session === null) return 'no session'
    return `forward ${session.forward.steps.length} step(s) · backward ${session.backward.steps.length} step(s) · ${meet(session) ? 'fingerprints MET — assemble when ready' : 'not met yet'}`
  }

  const onToggleMode = guard(() => {
    if (mode === 'edit') {
      if (goalLhs === null || goalRhs === null) {
        throw new Error('set both goal sides (LHS and RHS snapshots) before proving')
      }
      if (session === null) session = startSession(goalLhs, goalRhs, ctx)
      mode = 'prove'
      message = `PROVE mode: ${meetStatus()}`
    } else {
      mode = 'edit'
      message = 'EDIT mode'
    }
    sync()
  })
  const onToggleSide = guard(() => {
    if (mode !== 'prove') throw new Error('the forward/backward toggle applies in PROVE mode')
    side = side === 'forward' ? 'backward' : 'forward'
    message = `working ${side} — ${meetStatus()}`
    sync()
  })
  const onUndo = guard(() => {
    if (mode === 'edit') {
      const prev = editHistory.pop()
      if (prev === undefined) throw new Error('nothing to undo in edit mode')
      editDiagram = prev
      message = 'edit undone'
      sync()
      return
    }
    if (session === null) throw new Error('no active proof session')
    session = side === 'forward' ? undoForward(session) : undoBackward(session)
    message = `undone — ${meetStatus()}`
    sync()
  })
  const onAssemble = guard(() => {
    if (session === null) throw new Error('no active proof session')
    const name = nameInput.value.trim() === '' ? 'untitled' : nameInput.value.trim()
    const thm = assembleTheorem(session, name)
    checkTheorem(thm, ctx)
    // Adopt the theorem into the session context for citation and rebind the
    // shell's live ctx so saves, future citations, and applicableActions see it.
    session = adoptTheorem(session, thm)
    setContext(session.ctx, relations, constNames)
    message = `theorem '${name}' assembled, CHECKED, and ADOPTED (${thm.steps.length} step(s))`
    refreshChrome()
  })

  // ---- proof actions ----
  const applyF = (s: ProofStep): void => {
    if (session === null) throw new Error('no active proof session')
    session = applyForward(session, s)
    message = meetStatus()
    sync()
  }

  // ---- backward commit (reads inputs at click time) ----
  const commitBackward = (e: BackwardEntry): void => {
    if (session === null) throw new Error('no active proof session')
    switch (e.kind) {
      case 'unDoubleCut':
        session = applyBackward(session, { kind: 'unDoubleCut', outer: e.outer })
        break
      case 'unVacuousBubble':
        session = applyBackward(session, { kind: 'unVacuousBubble', bubble: e.bubble })
        break
      case 'unErase': {
        // Pattern read from the term input at commit time
        const termVal = termInput.value.trim()
        if (termVal === '') throw new Error('the term input is empty: type the pattern term first (\\ is λ)')
        const e0 = emptyDiagram()
        const { diagram } = addTermNode(e0, e0.root, parseTerm(termVal, constNames))
        session = applyBackward(session, {
          kind: 'unErase',
          region: e.region,
          pattern: mkDiagramWithBoundary(diagram, []),
          attachments: [],
        })
        break
      }
      case 'unConvert': {
        // Term and fuel read from inputs at commit time
        const termVal = termInput.value.trim()
        if (termVal === '') throw new Error('the term input is empty: type the target term first (\\ is λ)')
        const fuelVal = readCount(fuel.input, 'fuel')
        session = applyBackward(session, {
          kind: 'unConvert',
          node: e.node,
          term: parseTerm(termVal, constNames),
          fuel: fuelVal,
        })
        break
      }
      case 'unCite':
        // Collect args by clicking wires, then Commit dispatches applyBackward
        pending = { kind: 'unCite', name: e.name, sel: e.sel, args: [] }
        message = `un-cite '${e.name}': click the argument wires in boundary order, then Commit`
        refreshChrome()
        return
    }
    message = meetStatus()
    sync()
  }

  const commitAction = (a: ActionDescriptor, sel: SubgraphSelection): void => {
    if (session === null) throw new Error('no active proof session')
    switch (a.kind) {
      case 'erase':
        applyF({ rule: 'erasure', sel })
        return
      case 'insert': {
        const e0 = emptyDiagram()
        const { diagram } = addTermNode(e0, e0.root, parseInput())
        applyF({ rule: 'insertion', region: sel.region, pattern: mkDiagramWithBoundary(diagram, []), attachments: [], binders: {} })
        return
      }
      case 'doubleCutWrap':
        applyF({ rule: 'doubleCutIntro', sel })
        return
      case 'doubleCutElim':
        applyF({ rule: 'doubleCutElim', region: sel.regions[0]! })
        return
      case 'vacuousWrap':
        applyF({ rule: 'vacuousIntro', sel, arity: readCount(arity.input, 'bubble arity') })
        return
      case 'vacuousElim':
        applyF({ rule: 'vacuousElim', region: sel.regions[0]! })
        return
      case 'iterate':
        pending = { kind: 'iterate', sel }
        message = 'iterate: click the target region (empty space is the sheet)'
        refreshChrome()
        return
      case 'deiterate':
        applyF({ rule: 'deiteration', sel, fuel: readCount(fuel.input, 'fuel') })
        return
      case 'convert': {
        const node = sel.nodes[0]!
        const term = parseInput()
        const conv = applyConversion(currentDiagram(), node, term, readCount(fuel.input, 'fuel'))
        applyF({ rule: 'conversion', node, term, certificate: conv.certificate, attachments: {} })
        return
      }
      case 'instantiate': {
        const name = termInput.value.trim()
        const comp = relations[name]
        if (comp === undefined) {
          throw new Error(`unknown relation '${name}' — type a loaded relation name in the term input (loaded: ${Object.keys(relations).join(', ') || 'none'})`)
        }
        applyF({ rule: 'comprehensionInstantiate', bubble: sel.regions[0]!, comp, attachments: [], binders: {} })
        return
      }
      case 'relUnfold':
        applyF({ rule: 'relUnfold', node: sel.nodes[0]! })
        return
      case 'relFold': {
        const name = termInput.value.trim()
        if (!ctx.relations.has(name)) {
          throw new Error(`unknown relation '${name}' — type a loaded relation name in the term input (loaded: ${[...ctx.relations.keys()].join(', ') || 'none'})`)
        }
        pending = { kind: 'relFold', defId: name, sel, args: [] }
        message = `fold into '${name}': click the argument wires in boundary order, then Commit`
        refreshChrome()
        return
      }
      case 'citeTheorem':
        pending = { kind: 'cite', name: a.name, direction: a.direction, sel, args: [] }
        message = `cite '${a.name}': click the argument wires in boundary order, then Commit`
        refreshChrome()
        return
    }
  }

  // ---- clicks (selection + two-phase completion) ----
  const handleClick = (world: Vec2): void => {
    const hit = hitTest(engine, world)
    if (pending !== null && pending.kind === 'iterate') {
      const p = pending
      pending = null
      guard(() => {
        const target = hit === null ? displayed.root : hit.kind === 'region' ? hit.id : null
        if (target === null) throw new Error('iteration targets a region: click a cut/bubble or empty space for the sheet')
        applyF({ rule: 'iteration', sel: p.sel, target })
      })()
      return
    }
    if (pending !== null && (pending.kind === 'cite' || pending.kind === 'unCite' || pending.kind === 'relFold')) {
      const what = pending.kind === 'cite' ? `cite '${pending.name}'`
        : pending.kind === 'unCite' ? `un-cite '${pending.name}'`
        : `fold into '${pending.defId}'`
      if (hit !== null && hit.kind === 'wire') {
        pending.args.push(hit.id)
        message = `${what}: ${pending.args.length} argument wire(s) picked`
        refreshChrome()
      } else {
        message = `${what}: click wires only (or Commit/Cancel in the menu)`
        refreshChrome()
      }
      return
    }
    if (hit === null) {
      setHits([])
      return
    }
    const idx = hits.findIndex((h) => h.kind === hit.kind && h.id === hit.id)
    setHits(idx >= 0 ? hits.filter((_, i) => i !== idx) : [...hits, hit])
  }

  // ---- chrome refresh ----
  const refreshChrome = (): void => {
    const goal = `goal ${goalLhs === null ? 'LHS unset' : 'LHS set'}/${goalRhs === null ? 'RHS unset' : 'RHS set'}`
    const head = mode === 'edit' ? 'EDIT' : `PROVE·${side}`
    statusDiv.textContent = `[${head}] ${goal} | ${session === null ? 'no session' : meetStatus()} | ${message}`
    modeBtn.textContent = mode === 'edit' ? 'Switch to PROVE' : 'Switch to EDIT'
    sideBtn.textContent = side === 'forward' ? 'Side: forward (toggle)' : 'Side: backward (toggle)'

    menuDiv.replaceChildren()
    if (pending !== null) {
      const p = pending
      if (p.kind === 'cite') {
        menuDiv.append(button(`Commit citation of '${p.name}' (${p.args.length} arg(s))`, guard(() => {
          pending = null
          applyF({ rule: 'theorem', name: p.name, at: { sel: p.sel, args: [...p.args] }, direction: p.direction })
        })))
      }
      if (p.kind === 'unCite') {
        menuDiv.append(button(`Commit un-citation of '${p.name}' (${p.args.length} arg(s))`, guard(() => {
          if (session === null) throw new Error('no active proof session')
          pending = null
          session = applyBackward(session, { kind: 'unCite', name: p.name, at: { sel: p.sel, args: [...p.args] } })
          message = meetStatus()
          sync()
        })))
      }
      if (p.kind === 'relFold') {
        menuDiv.append(button(`Commit fold into '${p.defId}' (${p.args.length} arg(s))`, guard(() => {
          pending = null
          applyF({ rule: 'relFold', sel: p.sel, defId: p.defId, args: [...p.args] })
        })))
      }
      menuDiv.append(button('Cancel pending action', () => {
        pending = null
        message = 'pending action cancelled'
        refreshChrome()
      }))
      return
    }
    if (mode !== 'prove' || session === null || kernelSel === null) return
    const sel = kernelSel
    if (side === 'backward') {
      const entries = backwardEntries(currentDiagram(), sel, ctx)
      for (const e of entries) {
        menuDiv.append(button(e.label, guard(() => commitBackward(e))))
      }
      return
    }
    const all = applicableActions(currentDiagram(), sel, ctx)
    for (const a of all) {
      menuDiv.append(button(a.label, guard(() => commitAction(a, sel))))
    }
  }

  // ---- rendering ----
  // Highlight shapes for a hit, drawn over the painted engine. Node/region get
  // a ring; a wire gets its stroked spline(s). Hover-group highlighting (the
  // binder-hue tether replacement) is Task 2.
  const itemShapes = (hit: Hit, stroke: string): Shape[] => {
    if (hit.kind === 'node') {
      const b = engine.bodies.get(hit.id)
      return b === undefined ? [] : [{ kind: 'circle', center: b.pos, r: b.discR, fill: null, stroke, width: 2, insetColor: null, glow: null }]
    }
    if (hit.kind === 'region') {
      const g = engine.regions.get(hit.id)
      return g === undefined ? [] : [{ kind: 'circle', center: g.center, r: g.radius, fill: null, stroke, width: 2, insetColor: null, glow: null }]
    }
    const out: Shape[] = []
    for (const l of legPaths(engine)) {
      if (l.wid === hit.id) out.push({ kind: 'bezier', from: l.path.from, c1: l.path.c1, c2: l.path.c2, to: l.path.to, stroke, width: 3, glow: null })
    }
    for (const ex of boundaryExits(engine)) {
      if (ex.wid === hit.id) out.push({ kind: 'bezier', from: ex.path.from, c1: ex.path.c1, c2: ex.path.c2, to: ex.path.to, stroke, width: 3, glow: null })
    }
    for (const s of existentialStubs(engine)) {
      if (s.wid === hit.id) out.push({ kind: 'segment', from: s.from, to: s.to, stroke, width: 3, glow: null })
    }
    return out
  }

  const frame = (): void => {
    if (disposed) return
    if (canvas.width !== window.innerWidth || canvas.height !== window.innerHeight) {
      canvas.width = window.innerWidth
      canvas.height = window.innerHeight
    }
    for (let i = 0; i < SETTLE_STEPS_PER_FRAME; i++) {
      settleStep(engine)
      // drag pins the grabbed body: hold it at the cursor and relax around it
      if (pin !== null) {
        const b = engine.bodies.get(pin.node)
        if (b !== undefined) { b.pos = pin.pos; b.vel = vec(0, 0) }
      }
    }
    const shapes: Shape[] = paint(engine, theme)
    for (const h of hits) shapes.push(...itemShapes(h, SELECT_STROKE))
    if (hoverWorld !== null) {
      const hov = hitTest(engine, hoverWorld)
      if (hov !== null) shapes.push(...itemShapes(hov, HOVER_STROKE))
    }
    ctx2d.clearRect(0, 0, canvas.width, canvas.height)
    drawShapes(ctx2d, shapes, view)
    raf = requestAnimationFrame(frame)
  }

  // ---- pointer + wheel ----
  const screenOf = (e: PointerEvent | WheelEvent): Vec2 => {
    const r = canvas.getBoundingClientRect()
    return vec(e.clientX - r.left, e.clientY - r.top)
  }
  const onPointerDown = (e: PointerEvent): void => {
    const screen = screenOf(e)
    downScreen = screen
    dragMoved = false
    const hit = hitTest(engine, toWorld(screen))
    drag = hit !== null && hit.kind === 'node'
      ? { kind: 'node', node: hit.id }
      : { kind: 'pan', startOffset: { x: view.offsetX, y: view.offsetY }, startScreen: screen }
    canvas.setPointerCapture(e.pointerId)
  }
  const onPointerMove = (e: PointerEvent): void => {
    const screen = screenOf(e)
    hoverWorld = toWorld(screen)
    if (downScreen === null || drag === null) return
    if (!dragMoved && length(sub(screen, downScreen)) > CLICK_SLOP_PX) dragMoved = true
    if (!dragMoved) return
    if (drag.kind === 'node') {
      pin = { node: drag.node, pos: toWorld(screen) }
    } else {
      view.offsetX = drag.startOffset.x + (screen.x - drag.startScreen.x)
      view.offsetY = drag.startOffset.y + (screen.y - drag.startScreen.y)
    }
  }
  const onPointerUp = (e: PointerEvent): void => {
    const screen = screenOf(e)
    if (downScreen !== null && !dragMoved) handleClick(toWorld(screen))
    drag = null
    downScreen = null
    dragMoved = false
    pin = null // release: the pin lifts, physics resettles
  }
  const onWheel = (e: WheelEvent): void => {
    e.preventDefault()
    const screen = screenOf(e)
    const world = toWorld(screen)
    view.scale *= Math.exp(-e.deltaY * ZOOM_PER_WHEEL_PX)
    // keep the world point under the cursor fixed
    view.offsetX = screen.x - world.x * view.scale
    view.offsetY = screen.y - world.y * view.scale
  }

  // ---- persistence ----
  const onSave = guard(() => {
    const theory = sessionTheory(ctx, { relations })
    const json = theoryToJson(theory)
    const blob = new Blob([JSON.stringify(json, null, 2)], { type: 'application/json' })
    const url = URL.createObjectURL(blob)
    const a = document.createElement('a')
    a.href = url
    a.download = 'theory.json'
    document.body.append(a)
    a.click()
    document.body.removeChild(a)
    URL.revokeObjectURL(url)
    message = 'theory saved'
    refreshChrome()
  })

  const onLoad = guard(() => {
    const fileInput = document.createElement('input')
    fileInput.type = 'file'
    fileInput.accept = 'application/json'
    fileInput.addEventListener('change', () => {
      const file = fileInput.files?.[0]
      if (file === undefined) return
      const reader = new FileReader()
      reader.addEventListener('load', () => {
        try {
          const text = reader.result
          if (typeof text !== 'string') throw new Error('file read failed')
          const parsed = JSON.parse(text)
          // loadTheory re-verifies — the only road in; replace context only on success
          const loaded = loadTheory(parsed)
          setContext(loaded.ctx, loaded.theory.relations, new Set(Object.keys(loaded.ctx.definitions)))
          message = 'theory loaded successfully'
          refreshChrome()
        } catch (e) {
          message = e instanceof Error ? e.message : String(e)
          refreshChrome()
        }
      })
      reader.readAsText(file)
    })
    fileInput.click()
  })

  // ---- assemble the chrome ----
  editRow.append(
    termInput,
    button('Add term', onAddTerm),
    button('Wrap in cut', onWrapCut),
    button('Wrap in bubble', onWrapBubble),
    arity.wrap,
    button('Delete selection', onDelete),
    button('Join two wires', onJoinWires),
  )
  goalRow.append(
    button('Set goal LHS', onSetLhs),
    button('Set goal RHS', onSetRhs),
  )
  const modeBtn = button('Switch to PROVE', onToggleMode)
  const sideBtn = button('Side: forward (toggle)', onToggleSide)
  goalRow.append(modeBtn, sideBtn, button('Undo', onUndo))
  proveRow.append(fuel.wrap, nameInput, button('Assemble + check', onAssemble), button('Save theory', onSave), button('Load theory', onLoad))
  chrome.append(statusDiv, editRow, goalRow, proveRow, menuDiv, theoremsDiv)
  renderTheoremList()

  canvas.addEventListener('pointerdown', onPointerDown)
  canvas.addEventListener('pointermove', onPointerMove)
  canvas.addEventListener('pointerup', onPointerUp)
  canvas.addEventListener('wheel', onWheel, { passive: false })

  // ---- E2E debug seam: window.__vpaDebug hook when ?debug in URL ----
  if (new URLSearchParams(location.search).has('debug')) {
    ;(window as any).__vpaDebug = {
      nodeCount(): number {
        return Object.keys(displayed.nodes).length
      },
      status(): string {
        return message
      },
    }
  }

  refreshChrome()
  raf = requestAnimationFrame(frame)

  return {
    dispose(): void {
      disposed = true
      cancelAnimationFrame(raf)
      canvas.removeEventListener('pointerdown', onPointerDown)
      canvas.removeEventListener('pointermove', onPointerMove)
      canvas.removeEventListener('pointerup', onPointerUp)
      canvas.removeEventListener('wheel', onWheel)
      chrome.replaceChildren()
      if ((window as any).__vpaDebug !== undefined) delete (window as any).__vpaDebug
    },
  }
}
