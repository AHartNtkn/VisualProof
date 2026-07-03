import type { Diagram, Endpoint, NodeId, RegionId, WireId } from '../kernel/diagram/diagram'
import type { DiagramWithBoundary } from '../kernel/diagram/boundary'
import { mkDiagramWithBoundary } from '../kernel/diagram/boundary'
import type { Term } from '../kernel/term/term'
import { parseTerm } from '../kernel/term/parse'
import type { SubgraphSelection } from '../kernel/diagram/subgraph/selection'
import { polarity } from '../kernel/diagram/regions'
import { exploreForm } from '../kernel/diagram/canonical/explore'
import { applyConversion } from '../kernel/rules/conversion'
import { applyRelFold, applyRelUnfold } from '../kernel/rules/reldef'
import type { ProofContext, ProofStep } from '../kernel/proof/step'
import { checkTheorem } from '../kernel/proof/theorem'
import type { Vec2 } from '../view/vec'
import { vec, length, sub } from '../view/vec'
import type { Engine } from '../view/engine'
import { mkEngine, carryOver, subtreeCarriers } from '../view/engine'
import { settleStep } from '../view/relax'
import { legPaths, boundaryExits, existentialStubs } from '../view/wires'
import type { Shape, Theme } from '../view/paint'
import { paint, highlightGroup, nextTheme, LIGHT } from '../view/paint'
import { drawShapes } from '../view/canvas'
import { fitCamera, DESIGN_SCALE } from '../view/camera'
import type { Library } from './library'
import { emptyLibrary, reconcile, loadEntry, unloadEntry, adoptEntry, defineEntry, rebuild } from './library'
import { defineRelation, canonicalArgOrder, inferFoldArgs } from './define'
import type { Replay } from './replay'
import { mkReplay } from './replay'
import { emptyDiagram, addTermNode, addRefNode, addCut, addBubble, joinPorts, deleteSelection } from './edit'
import type { ProofSession } from './session'
import { startSession, applyForward, applyBackward, undoForward, undoBackward, meet, assembleTheorem, adoptTheorem, sideBoundary } from './session'
import { sessionTheory } from './persist'
import { theoryToJson } from '../kernel/proof/store'
import type { DragTarget, Hit } from './hittest'
import { hitTest, dragTarget, buildSelection } from './hittest'
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
  | { readonly kind: 'defineRelation'; readonly sel: SubgraphSelection; readonly args: WireId[]; name: string }
  | { readonly kind: 'foldChoose'; readonly sel: SubgraphSelection }
  | { readonly kind: 'addRelChoose' }

/** A grab: the bodies moved by this drag, each with its offset from the
    cursor's world position at grab time (so a drag moves, never teleports). */
type Drag = { readonly bodies: ReadonlyMap<string, Vec2> }

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

export async function mountShell(opts: ShellOptions): Promise<{ dispose(): void }> {
  const { canvas, chrome } = opts
  const ctx2d = canvas.getContext('2d')
  if (ctx2d === null) throw new Error('the canvas has no 2d context')

  // ---- boot: nothing. The app has ZERO built-in knowledge of any theory file
  // and fetches nothing. The working context is empty until the user opens
  // files/folders through the Library panel. rebuild(empty) is the empty ctx. ----
  let library: Library = emptyLibrary()
  const boot = rebuild(library)
  let ctx: ProofContext = boot.ctx
  let relations: Readonly<Record<string, DiagramWithBoundary>> = boot.relations

  // ---- state ----
  let mode: 'edit' | 'prove' | 'replay' = 'edit'
  let side: 'forward' | 'backward' = 'forward'
  // Replay mode: step through a bundled theorem's recorded derivation. `replay`
  // caches every intermediate diagram; `replayK` is the displayed step; the
  // mode we came from is restored on exit. Read-only — no rule dispatches.
  let replay: Replay | null = null
  let replayK = 0
  let replayReturnMode: 'edit' | 'prove' = 'edit'
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
  // The pin stores the cursor in SCREEN space: the camera refits every frame,
  // so a world-space pin would drift off the cursor whenever the fit moves.
  let pin: { readonly drag: Drag; screen: Vec2 } | null = null
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
  // There is NO pan: the camera is a fit — centered on the sheet circle with
  // a scale that keeps the whole sheet on screen (never past the design's
  // unit scale, so small sheets don't blow up) times the user's wheel-zoom
  // factor. It is recomputed every frame and STABILIZES because settled
  // layouts are at rest; the user cannot move the background, only zoom it.
  const view = { scale: DESIGN_SCALE, offsetX: canvas.width / 2, offsetY: canvas.height / 2 }
  let userZoom = 1
  const fitView = (): void => {
    const cam = fitCamera(engine.regions.get(engine.d.root), canvas.width, canvas.height, userZoom)
    view.scale = cam.scale
    view.offsetX = cam.offsetX
    view.offsetY = cam.offsetY
  }

  const toWorld = (screen: Vec2): Vec2 =>
    vec((screen.x - view.offsetX) / view.scale, (screen.y - view.offsetY) / view.scale)

  const currentDiagram = (): Diagram => {
    if (mode === 'replay' && replay !== null) return replay.diagramAt(replayK)
    if (mode === 'prove' && session !== null) {
      return side === 'forward' ? session.forward.current : session.backward.current
    }
    return editDiagram
  }

  // Prove-mode sides render their statement boundary as frame exits; an edit
  // sheet has no boundary. mkEngine ignores boundary ids absent from the
  // current diagram, so a stale id simply draws no exit.
  const currentBoundary = (): readonly WireId[] => {
    if (mode === 'replay' && replay !== null) return replay.boundary
    if (mode === 'prove' && session !== null) return sideBoundary(session, side)
    return []
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
  const libraryDiv = div('vpa-library')
  libraryDiv.id = 'library'

  // ---- Library panel state (browser-only view state) ----
  // The panel opens by default; each per-file detail group and the Session group
  // start collapsed. Load failures are stashed per file name (the empty string
  // keys the "Open file…" picker) and rendered inline, loudly, next to their
  // control. `dirHandle` is the session-lifetime workspace folder (no
  // persistence): opening or refreshing it re-lists its *.json files uniformly.
  let libraryOpen = true
  const expandedGroups = new Set<string>()
  const SESSION_GROUP = 'session' // sentinel; file groups are keyed 'file:<name>' so this cannot collide
  const loadErrors = new Map<string, string>()
  let dirHandle: FileSystemDirectoryHandle | null = null

  // ---- context rebinding ----
  // Called after every library change (load/unload/adopt): refreshes the live
  // context bindings the rest of the shell reads (citation menus, replay) and
  // re-renders the Library panel.
  const setContext = (newCtx: ProofContext, newRelations: Readonly<Record<string, DiagramWithBoundary>>): void => {
    ctx = newCtx
    relations = newRelations
    renderLibrary()
  }

  // Adopt a library change: rebuild the merged context from it and rebind live.
  // A rebuild conflict propagates through guard() to the status line, leaving
  // the prior library untouched.
  const applyLibrary = (next: Library): void => {
    library = next
    const r = rebuild(library)
    setContext(r.ctx, r.relations)
  }

  // The *.json file names directly inside a directory handle, sorted. Reads the
  // folder listing only — content is fetched lazily when a file is loaded.
  const listJsonFiles = async (dir: FileSystemDirectoryHandle): Promise<string[]> => {
    const names: string[] = []
    for await (const h of dir.values()) {
      if (h.kind === 'file' && h.name.endsWith('.json')) names.push(h.name)
    }
    return names.sort((a, b) => a.localeCompare(b))
  }

  // Open a workspace folder (File System Access API) and list its *.json files
  // uniformly. Dismissing the picker (AbortError) is not a failure.
  const onOpenFolder = (): void => {
    void (async () => {
      try {
        const handle = await window.showDirectoryPicker()
        dirHandle = handle
        library = reconcile(library, await listJsonFiles(handle))
        message = `opened workspace folder '${handle.name}' (${library.folder.length} .json file(s))`
        renderLibrary()
        refreshChrome()
      } catch (e) {
        if (e instanceof DOMException && e.name === 'AbortError') return
        message = e instanceof Error ? e.message : String(e)
        refreshChrome()
      }
    })()
  }

  // Re-read the open folder's listing (files added/removed on disk since).
  const onRefreshFolder = (): void => {
    if (dirHandle === null) return
    const handle = dirHandle
    void (async () => {
      try {
        library = reconcile(library, await listJsonFiles(handle))
        message = `refreshed workspace folder '${handle.name}'`
        renderLibrary()
        refreshChrome()
      } catch (e) {
        message = e instanceof Error ? e.message : String(e)
        refreshChrome()
      }
    })()
  }

  // Load a folder file: read its content lazily from the folder handle and bring
  // it in through loadEntry. A read/verify/merge failure lands inline next to the
  // file's row, loudly; success clears any prior error for that file.
  const loadFolderFile = (file: string): void => {
    if (dirHandle === null) {
      loadErrors.set(file, 'no workspace folder is open')
      renderLibrary()
      return
    }
    const handle = dirHandle
    void (async () => {
      try {
        const fh = await handle.getFileHandle(file)
        const text = await (await fh.getFile()).text()
        applyLibrary(loadEntry(library, file, JSON.parse(text)))
        loadErrors.delete(file)
        renderLibrary()
      } catch (e) {
        loadErrors.set(file, e instanceof Error ? e.message : String(e))
        renderLibrary()
      }
    })()
  }

  // Bring a single opened File (from the "Open file…" input) in through the same
  // loadEntry road, keyed by its own name. Errors land under the picker ('').
  const handleOpenedFile = (file: File): void => {
    const reader = new FileReader()
    reader.addEventListener('load', () => {
      try {
        const text = reader.result
        if (typeof text !== 'string') throw new Error('file read failed')
        applyLibrary(loadEntry(library, file.name, JSON.parse(text)))
        loadErrors.delete('')
        message = `loaded '${file.name}' into the library`
        refreshChrome()
      } catch (e) {
        loadErrors.set('', e instanceof Error ? e.message : String(e))
        renderLibrary()
      }
    })
    reader.readAsText(file)
  }

  // A collapsible detail group listing one loaded entry's (or the session's)
  // theorems and relations; each theorem carries a ▶ Replay button.
  const renderGroup = (
    key: string,
    title: string,
    thms: readonly { readonly name: string; readonly steps: number }[],
    relNames: readonly string[],
  ): HTMLElement => {
    const g = div('vpa-lib-group')
    const open = expandedGroups.has(key)
    g.append(button(`${open ? '▾' : '▸'} ${title}`, () => {
      if (open) expandedGroups.delete(key)
      else expandedGroups.add(key)
      renderLibrary()
    }))
    if (!open) return g
    const thmRow = div('vpa-lib-detail')
    thmRow.append('theorems: ')
    if (thms.length === 0) thmRow.append('none')
    thms.forEach((t, i) => {
      if (i > 0) thmRow.append(', ')
      thmRow.append(`${t.name} (${t.steps} step${t.steps === 1 ? '' : 's'}) `)
      thmRow.append(button('▶ Replay', guard(() => enterReplay(t.name))))
    })
    g.append(thmRow)
    const relRow = div('vpa-lib-detail')
    relRow.append(`relations: ${relNames.join(', ') || 'none'}`)
    g.append(relRow)
    return g
  }

  const errorSpan = (key: string): HTMLElement | null => {
    const msg = loadErrors.get(key)
    if (msg === undefined) return null
    const s = document.createElement('span')
    s.className = 'vpa-lib-error'
    s.textContent = ` — load failed: ${msg}`
    return s
  }

  // Render the whole Library panel from `library`: a toggle header, then (when
  // open) the workspace controls (Open folder…/Refresh/Open file…), the uniform
  // file list (Load/Unload per file — no origin distinction), a detail group per
  // loaded entry, and the Session group for adopted theorems.
  const renderLibrary = (): void => {
    libraryDiv.replaceChildren()
    libraryDiv.append(button(`${libraryOpen ? '▾' : '▸'} Library`, () => {
      libraryOpen = !libraryOpen
      renderLibrary()
    }))
    if (!libraryOpen) return

    const controls = div('vpa-lib-row')
    controls.append(button('Open folder…', onOpenFolder))
    if (dirHandle !== null) controls.append(button('Refresh', onRefreshFolder))
    controls.append(button('Open file…', () => openFileInput.click()))
    const pickerErr = errorSpan('')
    if (pickerErr !== null) controls.append(pickerErr)
    libraryDiv.append(controls)

    const folderLine = div('vpa-lib-folder')
    folderLine.append(dirHandle === null ? 'No workspace folder open.' : `Workspace: ${dirHandle.name}`)
    libraryDiv.append(folderLine)

    const list = div('vpa-lib-list')
    list.append('Files: ')
    if (library.entries.length === 0) list.append('none — open a folder or a file')
    for (const e of library.entries) {
      const row = div('vpa-lib-row')
      // The button carries the file name (accessible + unambiguous): 'Load
      // <file>' toggles to 'Unload <file>' once loaded.
      if (e.status === 'available') {
        row.append(button(`Load ${e.file}`, () => loadFolderFile(e.file)))
      } else {
        row.append(button(`Unload ${e.file}`, guard(() => {
          applyLibrary(unloadEntry(library, e.file))
          loadErrors.delete(e.file)
          expandedGroups.delete(`file:${e.file}`)
        })))
      }
      const err = errorSpan(e.file)
      if (err !== null) row.append(err)
      list.append(row)
    }
    libraryDiv.append(list)

    for (const e of library.entries) {
      if (e.status !== 'loaded') continue
      const thms = [...e.ctx.theorems.values()].map((t) => ({ name: t.name, steps: t.steps.length }))
      libraryDiv.append(renderGroup(
        `file:${e.file}`, e.file, thms,
        Object.keys(e.theory.relations),
      ))
    }

    if (library.adopted.length > 0 || library.definedRelations.length > 0) {
      libraryDiv.append(renderGroup(
        SESSION_GROUP, 'Session (adopted + defined)',
        library.adopted.map((t) => ({ name: t.name, steps: t.steps.length })),
        library.definedRelations.map((r) => r.name),
      ))
    }
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
    return parseTerm(termInput.value)
  }

  const sync = (): void => {
    const d = currentDiagram()
    if (d !== displayed) {
      // diagram identity changed: rebuild the engine (layout never persists),
      // drop selection/pending/pin — their ids belong to the old diagram
      displayed = d
      engine = mkEngine(d, currentBoundary())
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
  const onAddRelation = guard(() => {
    requireEdit()
    if (ctx.relations.size === 0) throw new Error('no relations to add — define one or load a theory first')
    pending = { kind: 'addRelChoose' }
    message = 'add relation: choose one (spawns with fresh argument wires)'
    refreshChrome()
  })
  const spawnRelation = (name: string): void => {
    const body = ctx.relations.get(name)!
    const region = hits.length === 1 && hits[0]!.kind === 'region' ? hits[0]!.id : editDiagram.root
    const { diagram, node } = addRefNode(editDiagram, region, name, body.boundary.length)
    pending = null
    pushEdit(diagram)
    message = `added relation node '${node}' (${name}/${body.boundary.length}) in region '${region}'`
    refreshChrome()
  }
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

  // ---- replay stepping ----
  // Open the stepper over a bundled/adopted theorem, remembering the mode we
  // leave so exit restores it. Step 0 (the lhs) seeds a fresh engine.
  const enterReplay = (name: string): void => {
    const thm = ctx.theorems.get(name)
    if (thm === undefined) throw new Error(`unknown theorem '${name}'`)
    if (mode !== 'replay') replayReturnMode = mode
    replay = mkReplay(thm, ctx)
    replayK = 0
    mode = 'replay'
    displayed = replay.diagramAt(0)
    engine = mkEngine(displayed, replay.boundary)
    settleStep(engine)
    pin = null
    hits = []
    kernelSel = null
    pending = null
    message = `replay '${name}'`
    refreshChrome()
  }

  // Move to step k (clamped). The new engine carries over shared bodies' physics
  // from the old one so the layout GLIDES from where it was rather than
  // re-seeding — the whole point of the stepper. currentDiagram() returns the
  // cached diagram object, so an incidental sync() will not rebuild and scramble.
  const gotoReplayStep = (k: number): void => {
    if (replay === null) return
    replayK = Math.max(0, Math.min(replay.stepCount, k))
    const prevEngine = engine
    displayed = replay.diagramAt(replayK)
    const next = mkEngine(displayed, replay.boundary)
    carryOver(prevEngine, next)
    settleStep(next)
    engine = next
    pin = null
    hits = []
    kernelSel = null
    pending = null
    message = `step ${replayK}/${replay.stepCount}${replayK > 0 ? ` — ${replay.labelAt(replayK)}` : ''}`
    refreshChrome()
  }

  const exitReplay = (): void => {
    mode = replayReturnMode
    replay = null
    replayK = 0
    message = mode === 'edit' ? 'EDIT mode' : `PROVE mode: ${meetStatus()}`
    sync() // rebuilds the engine for the restored mode's diagram
  }

  const onToggleMode = guard(() => {
    if (mode === 'replay') {
      exitReplay()
      return
    }
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
    // Adopt into the session context (so this session can keep citing it) AND
    // into the library's Session group; applyLibrary rebuilds the merged context
    // and rebinds the shell's live ctx so saves, future citations, and the panel
    // all see the new theorem.
    session = adoptTheorem(session, thm)
    applyLibrary(adoptEntry(library, thm))
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
        const { diagram } = addTermNode(e0, e0.root, parseTerm(termVal))
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
          term: parseTerm(termVal),
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
        if (ctx.relations.size === 0) throw new Error('no relations to fold into — define one or load a theory first')
        pending = { kind: 'foldChoose', sel }
        message = 'fold: choose the relation — its argument wires are inferred by matching'
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

  // ---- define relation (EDIT mode, two-phase like relFold) ----
  // Enter the pending pick: the crossing wires clicked in order become the
  // relation's argument boundary. Defining never mutates the sheet.
  const enterDefineRelation = (sel: SubgraphSelection): void => {
    pending = { kind: 'defineRelation', sel, args: [], name: '' }
    message = 'define relation: name it, then Commit — the argument order is canonical unless you pick the crossing wires yourself'
    refreshChrome()
  }

  // ---- clicks (selection + two-phase completion) ----
  const handleClick = (world: Vec2): void => {
    // Replay is read-only: canvas clicks select nothing and dispatch no rule.
    if (mode === 'replay') return
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
    if (pending !== null && (pending.kind === 'cite' || pending.kind === 'unCite' || pending.kind === 'defineRelation')) {
      const what = pending.kind === 'cite' ? `cite '${pending.name}'`
        : pending.kind === 'unCite' ? `un-cite '${pending.name}'`
        : 'define relation'
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
    if (mode === 'replay' && replay !== null) {
      const rule = replayK === 0 ? '(start)' : replay.labelAt(replayK)
      statusDiv.textContent = `[REPLAY] step ${replayK}/${replay.stepCount} — ${rule} | ${message}`
    } else {
      const head = mode === 'edit' ? 'EDIT' : `PROVE·${side}`
      statusDiv.textContent = `[${head}] ${goal} | ${session === null ? 'no session' : meetStatus()} | ${message}`
    }
    modeBtn.textContent = mode === 'edit' ? 'Switch to PROVE' : mode === 'prove' ? 'Switch to EDIT' : 'Exit replay'
    sideBtn.textContent = side === 'forward' ? 'Side: forward (toggle)' : 'Side: backward (toggle)'

    menuDiv.replaceChildren()
    if (mode === 'replay' && replay !== null) {
      const prev = button('◀ Prev', () => gotoReplayStep(replayK - 1))
      const next = button('Next ▶', () => gotoReplayStep(replayK + 1))
      prev.disabled = replayK === 0
      next.disabled = replayK === replay.stepCount
      menuDiv.append(prev, next, button('Exit replay', exitReplay))
      return
    }
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
      if (p.kind === 'foldChoose') {
        for (const name of ctx.relations.keys()) {
          menuDiv.append(button(`Fold into '${name}'`, guard(() => {
            const psel = p.sel
            // the definition's boundary order is fixed, so which host wire
            // plays which argument is an occurrence match — inferred, never
            // hand-picked
            const args = inferFoldArgs(mode === 'edit' ? editDiagram : currentDiagram(), psel, name, ctx)
            if (mode === 'edit') {
              const next = applyRelFold(editDiagram, psel, name, args, ctx.relations)
              pending = null
              pushEdit(next)
              message = `folded into '${name}'`
              refreshChrome()
              return
            }
            pending = null
            applyF({ rule: 'relFold', sel: psel, defId: name, args })
          })))
        }
      }
      if (p.kind === 'addRelChoose') {
        for (const name of ctx.relations.keys()) {
          menuDiv.append(button(`Add '${name}'`, guard(() => spawnRelation(name))))
        }
      }
      if (p.kind === 'defineRelation') {
        // A DEDICATED name field: relation names never ride the term or
        // theorem inputs. Its value lives on the pending state so chrome
        // refreshes don't wipe it.
        const nameField = document.createElement('input')
        nameField.id = 'relation-name'
        nameField.placeholder = 'new relation name'
        nameField.value = p.name
        nameField.addEventListener('input', () => { p.name = nameField.value })
        menuDiv.append(nameField)
        const label = p.args.length > 0
          ? `Commit relation definition (${p.args.length} picked arg(s))`
          : 'Commit relation definition (canonical argument order)'
        menuDiv.append(button(label, guard(() => {
          const name = p.name.trim()
          // No picks = the canonical explorer order; picking the crossing
          // wires yourself overrides it. defineRelation gates the
          // name/pick/extraction; defineEntry re-checks against the whole
          // library. A refusal lands in the status line, pending intact.
          const order = p.args.length > 0 ? [...p.args] : canonicalArgOrder(editDiagram, p.sel)
          const { relation } = defineRelation(editDiagram, p.sel, order, name, ctx, relations)
          const next = defineEntry(library, name, relation)
          pending = null
          applyLibrary(next)
          message = `defined '${name}' (arity ${relation.boundary.length})`
          refreshChrome()
        })))
      }
      menuDiv.append(button('Cancel pending action', () => {
        pending = null
        message = 'pending action cancelled'
        refreshChrome()
      }))
      return
    }
    // EDIT mode: a valid selection offers "Define relation…" (names the
    // selection as a new relation; the sheet is unchanged by defining), plus
    // fold/unfold as CONSTRUCTION operations — relation references are
    // notation for their bodies, so folding while drawing carries no proof
    // obligation (the same definitional equivalence relFold/relUnfold apply
    // in proofs).
    if (mode === 'edit') {
      if (kernelSel !== null) {
        const sel = kernelSel
        menuDiv.append(button('Define relation…', guard(() => enterDefineRelation(sel))))
        menuDiv.append(button('Fold into a relation…', guard(() => {
          if (ctx.relations.size === 0) throw new Error('no relations to fold into — define one or load a theory first')
          pending = { kind: 'foldChoose', sel }
          message = 'fold: choose the relation — its argument wires are inferred by matching'
          refreshChrome()
        })))
        if (sel.nodes.length === 1 && sel.regions.length === 0 && sel.wires.length === 0
          && displayed.nodes[sel.nodes[0]!]?.kind === 'ref') {
          menuDiv.append(button('Unfold relation', guard(() => {
            pushEdit(applyRelUnfold(editDiagram, sel.nodes[0]!, ctx.relations))
            message = 'relation unfolded'
            refreshChrome()
          })))
        }
      }
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
  // Hover-group target: hovering an atom or its bubble highlights the WHOLE
  // binder group (bubble ring + every atom bound to it) in their shared hue.
  // Returns the binder region id, or null when the hit is not part of a group.
  const hoverGroupBinder = (hit: Hit): RegionId | null => {
    if (hit.kind === 'node') {
      const n = displayed.nodes[hit.id]
      return n !== undefined && n.kind === 'atom' ? n.binder : null
    }
    if (hit.kind === 'region') {
      const r = displayed.regions[hit.id]
      return r !== undefined && r.kind === 'bubble' ? hit.id : null
    }
    return null
  }

  // Highlight shapes for a hit, drawn over the painted engine. Node/region get
  // a ring; a wire gets its stroked spline(s).
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
    const pinnedIds = pin === null ? null : new Set(pin.drag.bodies.keys())
    for (let i = 0; i < SETTLE_STEPS_PER_FRAME; i++) {
      // a drag pins the grabbed carriers: hold them at their grab offsets from
      // the cursor and relax everything else around them (pinned bodies are
      // excluded from cohesion so the drag feels direct)
      settleStep(engine, pinnedIds)
      if (pin !== null) {
        const at = toWorld(pin.screen)
        for (const [id, off] of pin.drag.bodies) {
          const b = engine.bodies.get(id)
          if (b !== undefined) {
            b.pos = { x: at.x + off.x, y: at.y + off.y }
            b.vel = vec(0, 0)
          }
        }
      }
    }
    fitView()
    const shapes: Shape[] = paint(engine, theme)
    for (const h of hits) shapes.push(...itemShapes(h, SELECT_STROKE))
    if (hoverWorld !== null) {
      const hov = hitTest(engine, hoverWorld)
      if (hov !== null) {
        const binder = hoverGroupBinder(hov)
        if (binder !== null) shapes.push(...highlightGroup(engine, theme, binder))
        else shapes.push(...itemShapes(hov, HOVER_STROKE))
      }
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
  const grabAt = (world: Vec2): Drag | null => {
    const t: DragTarget | null = dragTarget(engine, world)
    if (t === null) return null
    const bodies = new Map<string, Vec2>()
    const ids = t.kind === 'body' ? [t.id] : subtreeCarriers(engine, t.id)
    for (const id of ids) {
      const b = engine.bodies.get(id)!
      bodies.set(id, vec(b.pos.x - world.x, b.pos.y - world.y))
    }
    return { bodies }
  }
  const onPointerDown = (e: PointerEvent): void => {
    const screen = screenOf(e)
    downScreen = screen
    dragMoved = false
    drag = grabAt(toWorld(screen))
    canvas.setPointerCapture(e.pointerId)
  }
  const onPointerMove = (e: PointerEvent): void => {
    const screen = screenOf(e)
    hoverWorld = toWorld(screen)
    if (downScreen === null || drag === null) return
    if (!dragMoved && length(sub(screen, downScreen)) > CLICK_SLOP_PX) dragMoved = true
    if (!dragMoved) return
    pin = { drag, screen }
  }
  const onPointerUp = (e: PointerEvent): void => {
    const screen = screenOf(e)
    if (downScreen !== null && !dragMoved) handleClick(toWorld(screen))
    drag = null
    downScreen = null
    dragMoved = false
    pin = null // release: the pin lifts, physics resettles
  }
  // Replay stepping by arrow keys. Inert outside replay mode; ignores keys while
  // a text/number input is focused so typing a term is never hijacked.
  const onKeyDown = (e: KeyboardEvent): void => {
    if (mode !== 'replay' || replay === null) return
    const el = document.activeElement
    if (el instanceof HTMLInputElement || el instanceof HTMLTextAreaElement) return
    if (e.key === 'ArrowRight') { gotoReplayStep(replayK + 1); e.preventDefault() }
    else if (e.key === 'ArrowLeft') { gotoReplayStep(replayK - 1); e.preventDefault() }
  }
  const onWheel = (e: WheelEvent): void => {
    e.preventDefault()
    // zoom about the fixed background origin (the canvas center) — the only
    // view DOF; cursor-anchored zoom would let the offsets drift with no pan
    // to recover them
    userZoom *= Math.exp(-e.deltaY * ZOOM_PER_WHEEL_PX)
  }

  // ---- persistence ----
  // Save the live theory. With a workspace folder open, write it INTO that
  // folder (File System Access writable) and refresh the listing so the new file
  // appears in the same uniform list — user-created content is indistinguishable
  // from anything else. With no folder open, fall back to a browser download.
  const onSave = (): void => {
    const json = JSON.stringify(theoryToJson(sessionTheory(ctx, { relations })), null, 2)
    if (dirHandle !== null) {
      const handle = dirHandle
      const base = nameInput.value.trim() || 'theory'
      const fname = base.endsWith('.json') ? base : `${base}.json`
      void (async () => {
        try {
          const fh = await handle.getFileHandle(fname, { create: true })
          const w = await fh.createWritable()
          await w.write(json)
          await w.close()
          library = reconcile(library, await listJsonFiles(handle))
          renderLibrary()
          message = `saved '${fname}' into workspace folder '${handle.name}'`
          refreshChrome()
        } catch (e) {
          message = e instanceof Error ? e.message : String(e)
          refreshChrome()
        }
      })()
      return
    }
    const blob = new Blob([json], { type: 'application/json' })
    const url = URL.createObjectURL(blob)
    const a = document.createElement('a')
    a.href = url
    a.download = 'theory.json'
    document.body.append(a)
    a.click()
    document.body.removeChild(a)
    URL.revokeObjectURL(url)
    message = 'theory downloaded (open a workspace folder to save into it)'
    refreshChrome()
  }

  // ---- assemble the chrome ----
  // The "Open file…" picker is a real hidden file input (works for users and is
  // drivable by tests via setInputFiles); its change reads the chosen file
  // through the same loadEntry road, then clears so the same file can re-open.
  const openFileInput = document.createElement('input')
  openFileInput.type = 'file'
  openFileInput.accept = 'application/json'
  openFileInput.id = 'open-file-input'
  openFileInput.style.display = 'none'
  openFileInput.addEventListener('change', () => {
    const file = openFileInput.files?.[0]
    if (file !== undefined) handleOpenedFile(file)
    openFileInput.value = ''
  })
  editRow.append(
    termInput,
    button('Add term', onAddTerm),
    button('Add relation', onAddRelation),
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
  // Theme toggle: view-only, persists for the session; paint reads `theme`
  // every frame, so flipping it re-styles the next frame with no rebuild.
  const themeBtn = button(`Theme: ${theme.name}`, () => {
    theme = nextTheme(theme)
    canvas.style.background = theme.canvas
    themeBtn.textContent = `Theme: ${theme.name}`
  })
  goalRow.append(modeBtn, sideBtn, themeBtn, button('Undo', onUndo))
  proveRow.append(fuel.wrap, nameInput, button('Assemble + check', onAssemble), button('Save theory', onSave))
  chrome.append(statusDiv, editRow, goalRow, proveRow, menuDiv, libraryDiv, openFileInput)
  renderLibrary()

  canvas.addEventListener('pointerdown', onPointerDown)
  canvas.addEventListener('pointermove', onPointerMove)
  canvas.addEventListener('pointerup', onPointerUp)
  canvas.addEventListener('wheel', onWheel, { passive: false })
  window.addEventListener('keydown', onKeyDown)

  // ---- E2E debug seam: window.__vpaDebug hook when ?debug in URL ----
  if (new URLSearchParams(location.search).has('debug')) {
    ;(window as any).__vpaDebug = {
      nodeCount(): number {
        return Object.keys(displayed.nodes).length
      },
      status(): string {
        return message
      },
      replay(): { mode: string; k: number; n: number; label: string; bodies: number } {
        return {
          mode,
          k: replayK,
          n: replay?.stepCount ?? 0,
          label: replay === null ? '' : replayK === 0 ? '(start)' : replay.labelAt(replayK),
          bodies: engine.bodies.size,
        }
      },
      view(): { scale: number; offsetX: number; offsetY: number } {
        return { ...view }
      },
      bodies(): { id: string; kind: string; x: number; y: number; r: number }[] {
        return [...engine.bodies.values()].map((b) => ({ id: b.id, kind: b.kind, x: b.pos.x, y: b.pos.y, r: b.discR }))
      },
      // Verified-hittable world points for every rendered wire — the locator the
      // e2e uses to click argument wires, exactly as bodies() locates nodes. Each
      // point is confirmed by the real hitTest to resolve back to its wire, so a
      // returned entry is guaranteed clickable; unhittable wires are omitted.
      wires(): { id: string; x: number; y: number }[] {
        const bez = (t: number, p: { from: Vec2; c1: Vec2; c2: Vec2; to: Vec2 }): Vec2 => {
          const u = 1 - t
          return vec(
            u * u * u * p.from.x + 3 * u * u * t * p.c1.x + 3 * u * t * t * p.c2.x + t * t * t * p.to.x,
            u * u * u * p.from.y + 3 * u * u * t * p.c1.y + 3 * u * t * t * p.c2.y + t * t * t * p.to.y,
          )
        }
        const out: { id: string; x: number; y: number }[] = []
        const take = (id: WireId, samples: Vec2[]): void => {
          for (const s of samples) {
            const h = hitTest(engine, s)
            if (h !== null && h.kind === 'wire' && h.id === id) {
              out.push({ id, x: s.x, y: s.y })
              return
            }
          }
        }
        for (const l of legPaths(engine)) take(l.wid, [bez(0.5, l.path), bez(0.4, l.path), bez(0.6, l.path)])
        for (const ex of boundaryExits(engine)) take(ex.wid, [bez(0.5, ex.path), bez(0.4, ex.path), bez(0.6, ex.path)])
        for (const st of existentialStubs(engine)) {
          take(st.wid, [vec((st.from.x + st.to.x) / 2, (st.from.y + st.to.y) / 2), st.dot, vec(st.from.x * 0.4 + st.to.x * 0.6, st.from.y * 0.4 + st.to.y * 0.6)])
        }
        return out
      },
      // The live saveable theory as JSON — the same object Save theory writes.
      theoryJson(): string {
        return JSON.stringify(theoryToJson(sessionTheory(ctx, { relations })))
      },
      // The EDIT sheet's canonical form: a structural fingerprint (not a node
      // count) an e2e uses to assert defining a relation leaves the sheet
      // untouched — the spec's "no diagram changes when a relation is defined".
      editForm(): string {
        return exploreForm(editDiagram)
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
      window.removeEventListener('keydown', onKeyDown)
      chrome.replaceChildren()
      if ((window as any).__vpaDebug !== undefined) delete (window as any).__vpaDebug
    },
  }
}
