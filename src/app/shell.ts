import type { Diagram, NodeId, RegionId, WireId } from '../kernel/diagram/diagram'
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
import { vec } from '../view/vec'
import type { Engine } from '../view/engine'
import { mkEngine, carryOver } from '../view/engine'
import { settleStep, establishProofFrame, establishProofSlotShift, seedProject } from '../view/relax'
import { computeLegs, legPaths, existentialStubs } from '../view/wires'
import type { Shape, Theme } from '../view/paint'
import { paint, highlightGroup, LIGHT, THEMES } from '../view/paint'
import { drawShapes } from '../view/canvas'
import { fitCamera } from '../view/camera'
import { seedBodyPlacement } from '../view/placement'
import type { Library } from './library'
import { emptyLibrary, reconcile, loadEntry, unloadEntry, adoptEntry, defineEntry, rebuild } from './library'
import { defineRelation, canonicalArgOrder, inferFoldArgs } from './define'
import type { Replay } from './replay'
import { mkReplay } from './replay'
import { emptyDiagram, addTermNode, addRefNode } from './edit'
import type { ProofSession } from './session'
import { startSession, applyForward, applyBackward, undoForward, undoBackward, meet, assembleTheorem, adoptTheorem, sideBoundary } from './session'
import type { Companion } from './companion'
import { companionFor } from './companion'
import { sessionTheory } from './persist'
import { theoryToJson } from '../kernel/proof/store'
import type { Hit } from './hittest'
import { hitTest, wireHitTest, buildSelection } from './hittest'
import { isHitSelected } from './interact/brush'
import { ConstructController } from './interact/construct'
import { SpawnCascade } from './interact/spawn'
import { InteractiveViewport, type KeySample, type PointerClaim, type PointerSample } from './interact/viewport'
import { FeedbackController, type FeedbackInput, type FeedbackState } from './feedback'
import type { ActionDescriptor } from './actions'
import { applicableActions } from './actions'

/**
 * The DOM shell: browser glue over the tested headless core (edit, session,
 * hittest, actions) and the view layer. Every decision branch here calls a
 * tested function; the shell itself owns only browser concerns — mode state,
 * the displayed diagram, selection, pending two-phase actions, physics
 * seeding, domain operations, and chrome wiring. The viewport controller owns
 * every canvas gesture and all transient interaction state.
 * Behavioral coverage is Plan 10d's E2E.
 */

export type ShellOptions = {
  readonly canvas: HTMLCanvasElement
  readonly chrome: HTMLElement
  readonly initialDiagram?: Diagram
  readonly themes?: readonly Theme[]
  readonly initialLibrary?: Library
  readonly initialDirectoryHandle?: FileSystemDirectoryHandle
  readonly initialLibraryErrors?: ReadonlyMap<string, string>
  readonly libraryRenderer?: LibraryRenderer
}

export type LibraryViewState = {
  readonly library: Library
  readonly folderName: string | null
  readonly errors: ReadonlyMap<string, string>
  readonly theme: Theme
}

export type LibraryViewActions = {
  readonly openFolder: () => void
  readonly rescanFolder: () => void
  readonly openFile: () => void
  readonly load: (file: string) => void
  readonly unload: (file: string) => void
  readonly replay: (theorem: string) => void
}

export type LibraryRenderer = (
  host: HTMLElement,
  state: LibraryViewState,
  actions: LibraryViewActions,
) => void

/** The construction-time legality projection (a discrete event, not a mover):
    seed the region circles, then separate the dense mkEngine spiral seed onto the
    feasible set so the budgeted descent starts LEGAL instead of wedging in a
    dense-overlap coordinate-descent trap. This is the plan-23 leading projection,
    which mkEngine cannot run itself (relax.ts imports engine.ts — circular); the
    shell already imports relax.ts, so it runs it after every seed. */
type Pending =
  | { readonly kind: 'iterate'; readonly sel: SubgraphSelection }
  | { readonly kind: 'cite'; readonly name: string; readonly direction: 'forward' | 'reverse'; readonly sel: SubgraphSelection; readonly args: WireId[] }
  | { readonly kind: 'unCite'; readonly name: string; readonly sel: SubgraphSelection; readonly args: WireId[] }
  | { readonly kind: 'defineRelation'; readonly sel: SubgraphSelection; readonly args: WireId[]; name: string }
  | { readonly kind: 'foldChoose'; readonly sel: SubgraphSelection }

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
  const themeCycle = opts.themes ?? THEMES
  if (themeCycle.length === 0) throw new Error('mountShell requires at least one theme')
  const ctx2d = canvas.getContext('2d')
  if (ctx2d === null) throw new Error('the canvas has no 2d context')

  // ---- boot: nothing. The app has ZERO built-in knowledge of any theory file
  // and fetches nothing. The working context is empty until the user opens
  // files/folders through the Library panel. rebuild(empty) is the empty ctx. ----
  let library: Library = opts.initialLibrary ?? emptyLibrary()
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
  let editDiagram = opts.initialDiagram ?? emptyDiagram()
  const editHistory: Diagram[] = []
  let goalLhs: DiagramWithBoundary | null = null
  let goalRhs: DiagramWithBoundary | null = null
  let session: ProofSession | null = null
  let kernelSel: SubgraphSelection | null = null
  let pending: Pending | null = null
  // The render engine is rebuilt whenever the displayed diagram identity
  // changes (layout never persists). Boundary wiring for proof sides is Task 2;
  // an edit sheet has no boundary, so [] is correct here.
  let themeIndex = 0
  let theme: Theme = themeCycle[themeIndex] ?? LIGHT
  let displayed: Diagram = editDiagram
  let engine: Engine = mkEngine(displayed, [])
  seedProject(engine)
  let interaction!: InteractiveViewport
  let construct!: ConstructController
  let spawnCascade!: SpawnCascade
  const feedback = new FeedbackController()
  feedback.report({
    kind: 'ambient',
    text: 'right-click to place, drag lines to join, W wraps, Delete removes',
    owner: { kind: 'control', id: 'mode' },
    persistence: 'state',
  })
  const reportFeedback = (next: FeedbackInput): void => {
    feedback.report(next)
    refreshChrome()
  }
  const clearFeedbackProblem = (problemId: string): void => {
    feedback.clearProblem(problemId)
    refreshChrome()
  }
  let disposed = false
  let raf = 0

  // ---- companion viewport (view-only "where you are going" pane) ----
  // A second canvas driven by the SAME frame() rAF: its own engine + fit camera,
  // rebuilt only when companionFor's diagram identity changes (carryOver
  // warm-start, exactly the replay discipline). Session-lifetime display mode
  // like the theme toggle. No pin/selection/hover ever touches it.
  let companionMode: 'hidden' | 'pip' | 'split' = 'pip'
  let companionEngine: Engine | null = null
  let companionShownDiagram: Diagram | null = null
  // How many times the companion engine has been (re)seeded via mkEngine. It is
  // the rebuild-discipline observable: a step that leaves the companion's target
  // diagram identity unchanged must NOT bump this (no reseed); a step that
  // changes the target bumps it by exactly one (a single carryOver warm-start).
  let companionRebuilds = 0
  const companionView = { scale: 1, offsetX: 0, offsetY: 0 }
  let companionStyleKey = ''

  const companionWrap = document.createElement('div')
  companionWrap.id = 'companion'
  const companionCanvas = document.createElement('canvas')
  companionCanvas.id = 'companion-canvas'
  companionCanvas.style.display = 'block'
  companionCanvas.style.width = '100%'
  companionCanvas.style.height = '100%'
  const companionLabel = document.createElement('div')
  companionLabel.id = 'companion-label'
  companionLabel.style.position = 'absolute'
  companionLabel.style.top = '2px'
  companionLabel.style.left = '6px'
  companionLabel.style.font = '12px sans-serif'
  companionLabel.style.padding = '1px 6px'
  companionLabel.style.borderRadius = '3px'
  companionLabel.style.background = 'rgba(255, 255, 255, 0.8)'
  companionLabel.style.color = '#222'
  companionLabel.style.pointerEvents = 'none'
  companionWrap.append(companionCanvas, companionLabel)
  document.body.append(companionWrap)
  const cctx = companionCanvas.getContext('2d')
  if (cctx === null) throw new Error('the companion canvas has no 2d context')

  canvas.width = window.innerWidth
  canvas.height = window.innerHeight
  const applyThemeBackdrop = (): void => {
    canvas.style.background = theme.canvas
    canvas.ownerDocument.documentElement.style.background = theme.canvas
    canvas.ownerDocument.body.style.background = theme.canvas
  }
  applyThemeBackdrop()
  // There is NO pan: the camera is a fit — centered on the sheet circle with
  // a scale that keeps the whole fixed sheet frame on screen, times the user's
  // bounded wheel-zoom factor. It is recomputed every frame and STABILIZES because settled
  // layouts are at rest; the user cannot move the background, only zoom it.
  const view = { scale: 1, offsetX: canvas.width / 2, offsetY: canvas.height / 2 }
  // Fit a camera onto an engine's sheet circle for a given viewport, writing the
  // transform into `out`. The one fit both the main view and the companion use —
  // the pure `fitCamera` math, no fork. The companion passes zoom 1 (view-only,
  // no wheel input reaches it).
  const applyFit = (eng: Engine, w: number, h: number, zoom: number, out: { scale: number; offsetX: number; offsetY: number }): void => {
    // Plan 24: fit the FIXED frame, not the breathing sheet circle — the viewport
    // is rock-steady while content settles inside a constant box (no jitter).
    const fit = eng.frame === null ? undefined : { center: eng.frame.center, radius: eng.frame.half }
    const cam = fitCamera(fit, w, h, zoom)
    out.scale = cam.scale
    out.offsetX = cam.offsetX
    out.offsetY = cam.offsetY
  }
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
  const loadErrors = new Map<string, string>(opts.initialLibraryErrors)
  let dirHandle: FileSystemDirectoryHandle | null = opts.initialDirectoryHandle ?? null

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
  // A rebuild conflict propagates through guard() to typed refusal feedback, leaving
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
        renderLibrary()
      } catch (e) {
        if (e instanceof DOMException && e.name === 'AbortError') return
        loadErrors.set('', e instanceof Error ? e.message : String(e))
        renderLibrary()
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
        renderLibrary()
      } catch (e) {
        loadErrors.set('', e instanceof Error ? e.message : String(e))
        renderLibrary()
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
        renderLibrary()
      } catch (e) {
        loadErrors.set('', e instanceof Error ? e.message : String(e))
        renderLibrary()
      }
    })
    reader.readAsText(file)
  }

  const onUnloadFile = (file: string): void => {
    try {
      applyLibrary(unloadEntry(library, file))
      loadErrors.delete(file)
      expandedGroups.delete(`file:${file}`)
      renderLibrary()
    } catch (error) {
      loadErrors.set(file, error instanceof Error ? error.message : String(error))
      renderLibrary()
    }
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
    if (opts.libraryRenderer !== undefined) {
      libraryDiv.replaceChildren()
      opts.libraryRenderer(libraryDiv, {
        library,
        folderName: dirHandle?.name ?? null,
        errors: new Map(loadErrors),
        theme,
      }, {
        openFolder: onOpenFolder,
        rescanFolder: onRefreshFolder,
        openFile: () => openFileInput.click(),
        load: loadFolderFile,
        unload: onUnloadFile,
        replay: (name) => {
          enterReplay(name)
          libraryDiv.dispatchEvent(new CustomEvent('vpa-library-replay', { bubbles: true }))
        },
      })
      return
    }
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
        row.append(button(`Unload ${e.file}`, () => onUnloadFile(e.file)))
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
      // The kernel's refusal message IS the UX copy — verbatim, with explicit ownership.
      const hits = interaction.selection
      reportFeedback({
        kind: 'refusal',
        text: e instanceof Error ? e.message : String(e),
        owner: hits.length > 0 ? { kind: 'selection', hits } : { kind: 'viewport' },
        persistence: 'transient',
      })
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

  const sync = (surfaceChanged = false, preserveSelection = false): void => {
    const d = currentDiagram()
    if (d !== displayed || surfaceChanged) {
      const priorSelection = preserveSelection ? interaction.selection : []
      interaction.cancelActiveGesture()
      // Diagram identity changed: preserve the transaction's fixed frame and
      // surviving layout, then re-solve THIS diagram's content scale inside it.
      const previous = engine
      displayed = d
      engine = mkEngine(d, currentBoundary())
      carryOver(previous, engine)
      seedProject(engine)
      if (surfaceChanged) interaction.resetSurface()
      else interaction.reconcileDiagram()
      kernelSel = null
      pending = null
      if (preserveSelection) {
        interaction.setSelection(priorSelection.filter((hit) =>
          hit.kind === 'node' ? displayed.nodes[hit.id] !== undefined
            : hit.kind === 'region' ? displayed.regions[hit.id] !== undefined
              : displayed.wires[hit.id] !== undefined))
      }
    }
    refreshChrome()
  }

  const selectionChanged = (next: readonly Hit[]): void => {
    if (next.length === 0) {
      kernelSel = null
    } else {
      try {
        kernelSel = buildSelection(displayed, next)
      } catch (e) {
        kernelSel = null
        reportFeedback({
          kind: 'refusal',
          text: e instanceof Error ? e.message : String(e),
          owner: { kind: 'selection', hits: next },
          persistence: 'transient',
        })
      }
    }
    refreshChrome()
  }

  // ---- edit operations (mkDiagram-validated surgery via edit.ts) ----
  const pushEdit = (d: Diagram, placement?: { readonly node: NodeId; readonly at: Vec2 }, preserveSelection = false): void => {
    editHistory.push(editDiagram)
    editDiagram = d
    sync(false, preserveSelection)
    if (placement !== undefined) seedBodyPlacement(engine, placement.node, placement.at)
  }
  const requireEdit = (): void => {
    if (mode !== 'edit') throw new Error('construction is an EDIT-mode operation; switch modes first')
  }
  // ---- goal + session ----
  const onSetLhs = guard(() => {
    requireEdit()
    goalLhs = mkDiagramWithBoundary(editDiagram, [])
    session = null
    reportFeedback({ kind: 'success', text: 'goal LHS snapshotted from the sheet', owner: { kind: 'control', id: 'lifecycle' }, persistence: 'transient' })
  })
  const onSetRhs = guard(() => {
    requireEdit()
    goalRhs = mkDiagramWithBoundary(editDiagram, [])
    session = null
    reportFeedback({ kind: 'success', text: 'goal RHS snapshotted from the sheet', owner: { kind: 'control', id: 'lifecycle' }, persistence: 'transient' })
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
    interaction.cancelActiveGesture()
    displayed = replay.diagramAt(0)
    engine = mkEngine(displayed, replay.boundary)
    // Size the fixed border ONCE from the PROOF-WIDE max content extent (USER RULING
    // 2026-07-06, option (a)): a replay's contents are ALL its steps, so one absolute
    // border fits every step and never resizes as the proof is stepped. Cheap
    // (~150 ms whole-proof scan). Established before seedProject, whose establishFrame
    // then no-ops; every later step carries this same frame via carryOver.
    const steps = Array.from({ length: replay.stepCount + 1 }, (_, k) => ({ diagram: replay!.diagramAt(k), boundary: replay!.boundary }))
    establishProofFrame(engine, steps)
    // proof-wide boundary slot-shift: align the fixed slots to where the ports sit,
    // once, so boundary wires take short exits instead of sweeping the frame. Carried
    // across steps by carryOver (slots never reorder mid-proof).
    engine.slotShift = establishProofSlotShift(engine.frame!, steps)
    seedProject(engine)
    interaction.resetSurface()
    kernelSel = null
    pending = null
    reportFeedback({ kind: 'mode', text: `replay '${name}'`, owner: { kind: 'control', id: 'mode' }, persistence: 'state' })
  }

  // Move to step k (clamped). The new engine carries over shared bodies' physics
  // from the old one so the layout GLIDES from where it was rather than
  // re-seeding — the whole point of the stepper. currentDiagram() returns the
  // cached diagram object, so an incidental sync() will not rebuild and scramble.
  const gotoReplayStep = (k: number): void => {
    if (replay === null) return
    interaction.cancelActiveGesture()
    replayK = Math.max(0, Math.min(replay.stepCount, k))
    const prevEngine = engine
    displayed = replay.diagramAt(replayK)
    const next = mkEngine(displayed, replay.boundary)
    carryOver(prevEngine, next)
    seedProject(next)
    engine = next
    interaction.reconcileDiagram()
    kernelSel = null
    pending = null
    reportFeedback({
      kind: 'history',
      text: `step ${replayK}/${replay.stepCount}${replayK > 0 ? ` — ${replay.labelAt(replayK)}` : ''}`,
      owner: { kind: 'control', id: 'history' },
      persistence: 'state',
    })
  }

  const exitReplay = (): void => {
    mode = replayReturnMode
    replay = null
    replayK = 0
    feedback.report({
      kind: 'mode',
      text: mode === 'edit' ? 'EDIT mode' : `PROVE mode: ${meetStatus()}`,
      owner: { kind: 'control', id: 'mode' },
      persistence: 'state',
    })
    sync(true) // rebuilds the engine for the restored mode's diagram
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
      feedback.report({ kind: 'mode', text: `PROVE mode: ${meetStatus()}`, owner: { kind: 'control', id: 'mode' }, persistence: 'state' })
    } else {
      mode = 'edit'
      feedback.report({ kind: 'mode', text: 'EDIT mode', owner: { kind: 'control', id: 'mode' }, persistence: 'state' })
    }
    sync(true)
  })
  const onToggleSide = guard(() => {
    if (mode !== 'prove') throw new Error('the forward/backward toggle applies in PROVE mode')
    side = side === 'forward' ? 'backward' : 'forward'
    feedback.report({ kind: 'mode', text: `working ${side} — ${meetStatus()}`, owner: { kind: 'control', id: 'mode' }, persistence: 'state' })
    sync(true)
  })
  const onUndo = guard(() => {
    if (mode === 'edit') {
      const prev = editHistory.pop()
      if (prev === undefined) throw new Error('nothing to undo in edit mode')
      editDiagram = prev
      feedback.report({ kind: 'history', text: 'edit undone', owner: { kind: 'control', id: 'history' }, persistence: 'transient' })
      sync()
      return
    }
    if (session === null) throw new Error('no active proof session')
    session = side === 'forward' ? undoForward(session) : undoBackward(session)
    feedback.report({ kind: 'history', text: `undone — ${meetStatus()}`, owner: { kind: 'control', id: 'history' }, persistence: 'transient' })
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
    reportFeedback({ kind: 'success', text: `theorem '${name}' assembled, CHECKED, and ADOPTED (${thm.steps.length} step(s))`, owner: { kind: 'control', id: 'theorem-name' }, persistence: 'transient' })
  })

  // ---- proof actions ----
  const applyF = (s: ProofStep): void => {
    if (session === null) throw new Error('no active proof session')
    session = applyForward(session, s)
    feedback.report({ kind: 'success', text: meetStatus(), owner: { kind: 'selection', hits: interaction.selection }, persistence: 'transient', affected: interaction.selection })
    sync()
  }

  // ---- backward commit (reads inputs at click time) ----
  const commitBackward = (e: BackwardEntry): void => {
    if (session === null) throw new Error('no active proof session')
    switch (e.kind) {
      case 'unDoubleCut':
        session = applyBackward(session, { rule: 'doubleCutElim', region: e.outer })
        break
      case 'unVacuousBubble':
        session = applyBackward(session, { rule: 'vacuousElim', region: e.bubble })
        break
      case 'unErase': {
        // Pattern read from the term input at commit time
        const termVal = termInput.value.trim()
        if (termVal === '') throw new Error('the term input is empty: type the pattern term first (\\ is λ)')
        const e0 = emptyDiagram()
        const { diagram } = addTermNode(e0, e0.root, parseTerm(termVal))
        session = applyBackward(session, {
          rule: 'insertion',
          region: e.region,
          pattern: mkDiagramWithBoundary(diagram, []),
          attachments: [],
          binders: {},
        })
        break
      }
      case 'unConvert': {
        // Term and fuel read from inputs at commit time
        const termVal = termInput.value.trim()
        if (termVal === '') throw new Error('the term input is empty: type the target term first (\\ is λ)')
        const fuelVal = readCount(fuel.input, 'fuel')
        // conversion is direction-free: build the certificate with the same
        // fueled search the forward flow uses, then submit the ordinary step
        const goal = session.backward.current
        const conv = applyConversion(goal, e.node, parseTerm(termVal), fuelVal)
        session = applyBackward(session, {
          rule: 'conversion',
          node: e.node,
          term: parseTerm(termVal),
          certificate: conv.certificate,
          attachments: {},
        })
        break
      }
      case 'unCite':
        // Collect args by clicking wires, then Commit dispatches applyBackward
        pending = { kind: 'unCite', name: e.name, sel: e.sel, args: [] }
        reportFeedback({ kind: 'guidance', text: `un-cite '${e.name}': click the argument wires in boundary order, then Commit`, owner: { kind: 'selection', hits: interaction.selection }, persistence: 'interaction' })
        return
    }
    feedback.report({ kind: 'success', text: meetStatus(), owner: { kind: 'selection', hits: interaction.selection }, persistence: 'transient', affected: interaction.selection })
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
        reportFeedback({ kind: 'guidance', text: 'iterate: click the target region (empty space is the sheet)', owner: { kind: 'selection', hits: interaction.selection }, persistence: 'interaction' })
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
        reportFeedback({ kind: 'guidance', text: 'fold: choose the relation — its argument wires are inferred by matching', owner: { kind: 'selection', hits: interaction.selection }, persistence: 'interaction' })
        return
      }
      case 'citeTheorem':
        pending = { kind: 'cite', name: a.name, direction: a.direction, sel, args: [] }
        reportFeedback({ kind: 'guidance', text: `cite '${a.name}': click the argument wires in boundary order, then Commit`, owner: { kind: 'selection', hits: interaction.selection }, persistence: 'interaction' })
        return
    }
  }

  // ---- define relation (EDIT mode, two-phase like relFold) ----
  // Enter the pending pick: the crossing wires clicked in order become the
  // relation's argument boundary. Defining never mutates the sheet.
  const enterDefineRelation = (sel: SubgraphSelection): void => {
    pending = { kind: 'defineRelation', sel, args: [], name: '' }
    reportFeedback({ kind: 'guidance', text: 'define relation: name it, then Commit — the argument order is canonical unless you pick the crossing wires yourself', owner: { kind: 'selection', hits: interaction.selection }, persistence: 'interaction' })
  }

  // ---- domain pointer claims (selection is owned by InteractiveViewport) ----
  const handleClaimedClick = (world: Vec2): void => {
    const hit = hitTest(engine, world, { scale: view.scale })
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
        reportFeedback({ kind: 'guidance', text: `${what}: ${pending.args.length} argument wire(s) picked`, owner: { kind: 'hit', hit }, persistence: 'interaction' })
      } else {
        reportFeedback({ kind: 'guidance', text: `${what}: click wires only (or Commit/Cancel in the menu)`, owner: { kind: 'point', point: world }, persistence: 'interaction' })
      }
      return
    }
  }

  const claimPointer = (sample: PointerSample): PointerClaim | null => {
    const pendingClaim: PointerClaim | null = sample.button === 0 && pending !== null && (
      pending.kind === 'iterate'
      || pending.kind === 'cite'
      || pending.kind === 'unCite'
      || pending.kind === 'defineRelation'
    ) ? {
        still: 'claim',
        blocksPassiveRelaxation: false,
        move: () => {},
        release: (at, moved) => { if (!moved) handleClaimedClick(at.world) },
        cancel: () => {},
      } : null
    return pendingClaim ?? construct.claim(sample)
  }

  // ---- chrome refresh ----
  const refreshChrome = (): void => {
    const message = feedback.snapshot().current?.text ?? ''
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
          session = applyBackward(session, { rule: 'theorem', name: p.name, at: { sel: p.sel, args: [...p.args] }, direction: 'reverse' })
          feedback.report({ kind: 'success', text: meetStatus(), owner: { kind: 'selection', hits: interaction.selection }, persistence: 'transient', affected: interaction.selection })
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
              reportFeedback({ kind: 'success', text: `folded into '${name}'`, owner: { kind: 'selection', hits: interaction.selection }, persistence: 'transient', affected: interaction.selection })
              return
            }
            pending = null
            applyF({ rule: 'relFold', sel: psel, defId: name, args })
          })))
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
          // library. A refusal stays attached to this pending interaction.
          const order = p.args.length > 0 ? [...p.args] : canonicalArgOrder(editDiagram, p.sel)
          const { relation } = defineRelation(editDiagram, p.sel, order, name, ctx, relations)
          const next = defineEntry(library, name, relation)
          pending = null
          applyLibrary(next)
          reportFeedback({ kind: 'success', text: `defined '${name}' (arity ${relation.boundary.length})`, owner: { kind: 'control', id: 'relation-name' }, persistence: 'transient' })
        })))
      }
      menuDiv.append(button('Cancel pending action', () => {
        pending = null
        reportFeedback({ kind: 'history', text: 'pending action cancelled', owner: { kind: 'control', id: 'action-menu' }, persistence: 'transient' })
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
          reportFeedback({ kind: 'guidance', text: 'fold: choose the relation — its argument wires are inferred by matching', owner: { kind: 'selection', hits: interaction.selection }, persistence: 'interaction' })
        })))
        if (sel.nodes.length === 1 && sel.regions.length === 0 && sel.wires.length === 0
          && displayed.nodes[sel.nodes[0]!]?.kind === 'ref') {
          menuDiv.append(button('Unfold relation', guard(() => {
            pushEdit(applyRelUnfold(editDiagram, sel.nodes[0]!, ctx.relations))
            reportFeedback({ kind: 'success', text: 'relation unfolded', owner: { kind: 'selection', hits: interaction.selection }, persistence: 'transient', affected: interaction.selection })
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
      // scale the highlight ring by e.scale to match the drawn/hit disc size
      return b === undefined ? [] : [{ kind: 'circle', center: b.pos, r: b.discR * engine.scale, fill: null, stroke, width: 2, insetColor: null, glow: null }]
    }
    if (hit.kind === 'region') {
      const g = engine.regions.get(hit.id)
      return g === undefined ? [] : [{ kind: 'circle', center: g.center, r: g.radius, fill: null, stroke, width: 2, insetColor: null, glow: null }]
    }
    const out: Shape[] = []
    // Every wire (junctions included) is its elastica legs — trace the SAME legs
    // paint draws, so the hover outline matches exactly.
    for (const l of legPaths(engine)) {
      if (l.wid === hit.id) out.push({ kind: 'polyline', pts: l.pts, stroke, width: 3, glow: null })
    }
    for (const s of existentialStubs(engine)) {
      if (s.wid === hit.id) out.push({ kind: 'segment', from: s.from, to: s.to, stroke, width: 3, glow: null })
    }
    return out
  }

  // Position/show the companion wrapper for the current display mode. Plain CSS
  // sizing — PiP is a fixed-fraction bottom-right inset, split is the right half;
  // the queued interface overhaul restyles this. Only re-writes styles when the
  // visibility/mode key changes so an idle frame touches no layout.
  const restyleCompanion = (visible: boolean): void => {
    const key = visible ? companionMode : 'hidden'
    if (key === companionStyleKey) return
    companionStyleKey = key
    if (!visible) {
      companionWrap.style.display = 'none'
      return
    }
    companionWrap.style.display = 'block'
    companionWrap.style.position = 'fixed'
    companionWrap.style.zIndex = '1'
    companionWrap.style.boxSizing = 'border-box'
    companionWrap.style.background = theme.canvas
    if (companionMode === 'split') {
      companionWrap.style.top = '0'
      companionWrap.style.bottom = ''
      companionWrap.style.right = '0'
      companionWrap.style.width = '50vw'
      companionWrap.style.height = '100vh'
      companionWrap.style.border = ''
      companionWrap.style.borderLeft = '1px solid rgba(0, 0, 0, 0.2)'
      companionWrap.style.borderRadius = ''
    } else {
      companionWrap.style.top = ''
      companionWrap.style.bottom = '16px'
      companionWrap.style.right = '16px'
      companionWrap.style.width = '28vw'
      companionWrap.style.height = '28vh'
      companionWrap.style.borderLeft = ''
      companionWrap.style.border = '1px solid rgba(0, 0, 0, 0.25)'
      companionWrap.style.borderRadius = '4px'
    }
  }

  // Drive the companion pane for this frame: rebuild its engine ONLY when the
  // target diagram's identity changes (carryOver warm-start), settle, fit, paint.
  const renderCompanion = (comp: Companion | null, visible: boolean): void => {
    restyleCompanion(visible)
    if (!visible || comp === null) return
    companionWrap.style.background = theme.canvas
    const w = companionCanvas.clientWidth
    const h = companionCanvas.clientHeight
    if (w > 0 && h > 0 && (companionCanvas.width !== w || companionCanvas.height !== h)) {
      companionCanvas.width = w
      companionCanvas.height = h
    }
    if (comp.diagram !== companionShownDiagram || companionEngine === null) {
      const prev = companionEngine
      const next = mkEngine(comp.diagram, comp.boundary)
      if (prev !== null) carryOver(prev, next)
      seedProject(next)
      companionEngine = next
      companionShownDiagram = comp.diagram
      companionRebuilds++
    }
    settleStep(companionEngine, null)
    applyFit(companionEngine, companionCanvas.width, companionCanvas.height, 1, companionView)
    const shapes = paint(companionEngine, theme)
    cctx.clearRect(0, 0, companionCanvas.width, companionCanvas.height)
    cctx.fillStyle = theme.canvas
    cctx.fillRect(0, 0, companionCanvas.width, companionCanvas.height)
    drawShapes(cctx, shapes, companionView)
    companionLabel.textContent = comp.label
  }

  const markerAt = (id: string): Vec2 | null => {
    const b = engine.bodies.get(id)
    if (b === undefined) return null
    const r = b.discR * engine.scale
    return { x: b.pos.x + r * 0.72, y: b.pos.y - r * 0.72 }
  }
  const frame = (): void => {
    if (disposed) return
    const comp = companionFor({ mode, session, side, replay })
    const companionVisible = comp !== null && companionMode !== 'hidden'
    // Split gives the companion the right half, so the main view fits the left
    // half; PiP/hidden leave the main view full-width (PiP overlays a corner).
    const mainW = comp !== null && companionMode === 'split' ? Math.floor(window.innerWidth / 2) : window.innerWidth
    if (canvas.width !== mainW || canvas.height !== window.innerHeight) {
      canvas.width = mainW
      canvas.height = window.innerHeight
    }
    // Plan 24 motion policy: a FULL strict-descent sweep over every DOF each
    // frame (no time-slicing) — the whole diagram eases toward rest together.
    // InteractiveViewport supplies the exact persistent and active pin set.
    interaction.advance()
    const shapes: Shape[] = paint(engine, theme)
    for (const id of interaction.pins) {
      const b = engine.bodies.get(id)
      if (b === undefined) continue
      shapes.push({ kind: 'circle', center: b.pos, r: b.discR * engine.scale + 1.2, fill: null, stroke: theme.interaction.pin, width: 1.5, insetColor: null, glow: null })
      const at = markerAt(id)
      if (at !== null) shapes.push({ kind: 'dot', center: at, rPx: 5.5, fill: theme.interaction.pin })
    }
    const pinPreview = interaction.pinPreviewId
    const pinPreviewAt = pinPreview === null ? null : markerAt(pinPreview)
    if (pinPreviewAt !== null) shapes.push({ kind: 'dot', center: pinPreviewAt, rPx: 8, fill: theme.interaction.pin })
    for (const h of interaction.selection) shapes.push(...itemShapes(h, theme.interaction.selection))
    const hov = interaction.hover
    if (hov !== null) {
      const binder = hoverGroupBinder(hov)
      if (binder !== null) shapes.push(...highlightGroup(engine, theme, binder))
      else shapes.push(...itemShapes(hov, isHitSelected(interaction.selection, hov) ? theme.interaction.selectedHover : theme.interaction.hover))
    }
    shapes.push(...construct.overlay())
    ctx2d.clearRect(0, 0, canvas.width, canvas.height)
    ctx2d.fillStyle = theme.canvas
    ctx2d.fillRect(0, 0, canvas.width, canvas.height)
    drawShapes(ctx2d, shapes, view)
    renderCompanion(comp, companionVisible)
    raf = requestAnimationFrame(frame)
  }

  // Replay stepping by arrow keys. Inert outside replay mode; ignores keys while
  // a text/number input is focused so typing a term is never hijacked.
  const onKeyDown = (e: KeySample): boolean => {
    if (e.key === 'Escape' && spawnCascade.escape()) return true
    if (construct.keyDown(e)) return true
    if (e.key === 'Home') {
      interaction.resetZoom()
      return true
    }
    if (mode !== 'replay' || replay === null) return false
    if (e.key === 'ArrowRight') { gotoReplayStep(replayK + 1); return true }
    if (e.key === 'ArrowLeft') { gotoReplayStep(replayK - 1); return true }
    return false
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
          clearFeedbackProblem('save')
          reportFeedback({ kind: 'success', text: `saved '${fname}' into workspace folder '${handle.name}'`, owner: { kind: 'control', id: 'save' }, persistence: 'transient' })
        } catch (e) {
          reportFeedback({
            kind: 'problem',
            text: e instanceof Error ? e.message : String(e),
            owner: { kind: 'control', id: 'save' },
            persistence: 'problem',
            problemId: 'save',
          })
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
    reportFeedback({ kind: 'success', text: 'theory downloaded (open a workspace folder to save into it)', owner: { kind: 'control', id: 'save' }, persistence: 'transient' })
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
  goalRow.append(
    button('Set goal LHS', onSetLhs),
    button('Set goal RHS', onSetRhs),
  )
  const modeBtn = button('Switch to PROVE', onToggleMode)
  const sideBtn = button('Side: forward (toggle)', onToggleSide)
  // Theme toggle: view-only, persists for the session; paint reads `theme`
  // every frame, so flipping it re-styles the next frame with no rebuild.
  const themeBtn = button(`Theme: ${theme.name}`, () => {
    themeIndex = (themeIndex + 1) % themeCycle.length
    theme = themeCycle[themeIndex]!
    applyThemeBackdrop()
    themeBtn.textContent = `Theme: ${theme.name}`
    renderLibrary()
  })
  // Cycle the companion pane hidden → PiP → split. Session-lifetime, like the
  // theme toggle; the next frame reads companionMode and re-lays-out.
  const companionBtn = button(`Companion: ${companionMode}`, () => {
    companionMode = companionMode === 'hidden' ? 'pip' : companionMode === 'pip' ? 'split' : 'hidden'
    companionBtn.textContent = `Companion: ${companionMode}`
  })
  goalRow.append(modeBtn, sideBtn, themeBtn, companionBtn, button('Undo', onUndo))
  proveRow.append(termInput, arity.wrap, fuel.wrap, nameInput, button('Assemble + check', onAssemble), button('Save theory', onSave))
  chrome.append(statusDiv)
  chrome.append(editRow, goalRow, proveRow, menuDiv, libraryDiv, openFileInput)
  spawnCascade = new SpawnCascade({
    host: document.body,
    spawnTerm: ({ source, invocation }) => {
      try {
        const added = addTermNode(editDiagram, invocation.region, parseTerm(source))
        pushEdit(added.diagram, { node: added.node, at: invocation.world }, true)
        reportFeedback({ kind: 'success', text: 'term placed', owner: { kind: 'node', id: added.node }, affected: [{ kind: 'node', id: added.node }], persistence: 'transient' })
        return true
      } catch (error) {
        reportFeedback({ kind: 'refusal', text: error instanceof Error ? error.message : String(error), owner: { kind: 'point', point: invocation.world }, persistence: 'transient' })
        return false
      }
    },
    spawnRelation: ({ defId, arity: relationArity, invocation }) => {
      try {
        const relation = ctx.relations.get(defId)
        if (relation === undefined) throw new Error(`relation '${defId}' is no longer loaded`)
        if (relation.boundary.length !== relationArity) throw new Error(`relation '${defId}' changed while the spawn menu was open`)
        const added = addRefNode(editDiagram, invocation.region, defId, relationArity)
        pushEdit(added.diagram, { node: added.node, at: invocation.world }, true)
        reportFeedback({ kind: 'success', text: `relation '${defId}' placed`, owner: { kind: 'node', id: added.node }, affected: [{ kind: 'node', id: added.node }], persistence: 'transient' })
        return true
      } catch (error) {
        reportFeedback({ kind: 'refusal', text: error instanceof Error ? error.message : String(error), owner: { kind: 'point', point: invocation.world }, persistence: 'transient' })
        return false
      }
    },
  })
  construct = new ConstructController({
    host: document.body,
    active: () => mode === 'edit',
    engine: () => engine,
    viewScale: () => view.scale,
    diagram: () => editDiagram,
    selection: () => interaction.selection,
    setSelection: (selection) => interaction.setSelection(selection),
    commit: (diagram) => pushEdit(diagram),
    status: reportFeedback,
    clearProblem: clearFeedbackProblem,
    openSpawn: (sample, region) => spawnCascade.open({
      screen: sample.client,
      world: sample.world,
      region,
    }, ctx.relations),
    theme: () => theme,
  })
  editRow.append(construct.optionsElement)
  interaction = new InteractiveViewport({
    canvas,
    view,
    engine: () => engine,
    diagram: () => displayed,
    selectionEnabled: () => mode !== 'replay',
    claim: claimPointer,
    doubleClick: (sample) => construct.doubleClick(sample),
    keyDown: onKeyDown,
    selectionChanged,
    selectionCommitted: () => {
      pending = null
      feedback.clearInteraction()
      refreshChrome()
    },
    statusChanged: reportFeedback,
  })
  renderLibrary()

  const dispose = (): void => {
    if (disposed) return
    disposed = true
    cancelAnimationFrame(raf)
    interaction.dispose()
    construct.dispose()
    spawnCascade.dispose()
    chrome.replaceChildren()
    companionWrap.remove()
    if ((window as any).__vpaDebug !== undefined) delete (window as any).__vpaDebug
  }

  // ---- E2E debug seam: window.__vpaDebug hook when ?debug in URL ----
  if (new URLSearchParams(location.search).has('debug')) {
    ;(window as any).__vpaDebug = {
      nodeCount(): number {
        return Object.keys(displayed.nodes).length
      },
      status(): string {
        return feedback.snapshot().current?.text ?? ''
      },
      feedback(): FeedbackState {
        return feedback.snapshot()
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
      interaction(): { selected: readonly Hit[]; pins: string[]; userZoom: number } {
        return {
          selected: interaction.selection,
          pins: [...interaction.pins],
          userZoom: interaction.userZoom,
        }
      },
      bodies(): { id: string; kind: string; x: number; y: number; r: number; region: string }[] {
        return [...engine.bodies.values()].map((b) => ({ id: b.id, kind: b.kind, x: b.pos.x, y: b.pos.y, r: b.discR, region: b.region }))
      },
      diagram(): {
        nodes: { id: string; kind: string; region: string; defId: string | null }[]
        wires: { id: string; scope: string; endpoints: number }[]
        regions: { id: string; kind: string; parent: string | null }[]
      } {
        return {
          nodes: Object.entries(displayed.nodes).map(([id, node]) => ({
            id,
            kind: node.kind,
            region: node.region,
            defId: node.kind === 'ref' ? node.defId : null,
          })),
          wires: Object.entries(displayed.wires).map(([id, wire]) => ({ id, scope: wire.scope, endpoints: wire.endpoints.length })),
          regions: Object.entries(displayed.regions).map(([id, region]) => ({
            id,
            kind: region.kind,
            parent: region.kind === 'sheet' ? null : region.parent,
          })),
        }
      },
      // Derived region circles (the drawn cut/bubble outlines) — the e2e uses these
      // to assert HARD SEMANTIC CONTAINMENT (a dragged node never enters a cut
      // circle it is not a member of).
      regions(): { id: string; kind: string; parent: string | null; x: number; y: number; r: number }[] {
        return [...engine.regions.entries()].map(([id, g]) => {
          const reg = displayed.regions[id]
          return { id, kind: reg?.kind ?? '?', parent: reg !== undefined && reg.kind !== 'sheet' ? reg.parent : null, x: g.center.x, y: g.center.y, r: g.radius }
        })
      },
      // Verified-hittable world points for every rendered wire — the locator the
      // e2e uses to click argument wires, exactly as bodies() locates nodes. Each
      // point is confirmed by the real hitTest to resolve back to its wire, so a
      // returned entry is guaranteed clickable; unhittable wires are omitted.
      wires(): { id: string; x: number; y: number; dx: number; dy: number }[] {
        // sample a traced polyline near its middle (where a leg is most
        // clickable — away from disc rims and slots)
        const mids = (pts: Vec2[]): { point: Vec2; direction: Vec2 }[] => {
          const n = pts.length
          if (n === 0) return []
          const at = (f: number): { point: Vec2; direction: Vec2 } => {
            const i = Math.max(0, Math.min(n - 1, Math.round(f * (n - 1))))
            const before = pts[Math.max(0, i - 1)]!
            const after = pts[Math.min(n - 1, i + 1)]!
            return { point: pts[i]!, direction: { x: after.x - before.x, y: after.y - before.y } }
          }
          return [at(0.5), at(0.4), at(0.6)]
        }
        const out: { id: string; x: number; y: number; dx: number; dy: number }[] = []
        const take = (id: WireId, samples: { point: Vec2; direction: Vec2 }[]): void => {
          for (const s of samples) {
            const h = hitTest(engine, s.point, { scale: view.scale })
            if (h !== null && h.kind === 'wire' && h.id === id) {
              out.push({ id, x: s.point.x, y: s.point.y, dx: s.direction.x, dy: s.direction.y })
              return
            }
          }
        }
        for (const l of legPaths(engine)) take(l.wid, mids(l.pts))
        for (const st of existentialStubs(engine)) {
          const direction = { x: st.to.x - st.from.x, y: st.to.y - st.from.y }
          take(st.wid, [
            { point: vec((st.from.x + st.to.x) / 2, (st.from.y + st.to.y) / 2), direction },
            { point: st.dot, direction },
            { point: vec(st.from.x * 0.4 + st.to.x * 0.6, st.from.y * 0.4 + st.to.y * 0.6), direction },
          ])
        }
        return out
      },
      wireBinds(): { id: string; node: string; x: number; y: number }[] {
        const out: { id: string; node: string; x: number; y: number }[] = []
        for (const geometry of computeLegs(engine)) {
          const candidates = [
            { end: geometry.leg.from, point: geometry.pts[0] },
            { end: geometry.leg.to, point: geometry.pts.at(-1) },
          ]
          for (const candidate of candidates) {
            if (candidate.point === undefined || displayed.nodes[candidate.end.body] === undefined) continue
            const general = hitTest(engine, candidate.point, { scale: view.scale })
            const wire = wireHitTest(engine, candidate.point, { scale: view.scale })
            if (general?.kind === 'node' && general.id === candidate.end.body && wire?.id === geometry.leg.wid) {
              out.push({ id: geometry.leg.wid, node: candidate.end.body, x: candidate.point.x, y: candidate.point.y })
            }
          }
        }
        return out
      },
      // The companion pane's live decision + engine, for the e2e: null when the
      // companion is not applicable (EDIT / no session / no replay), else the
      // label, whether it is on-screen, and its engine body count.
      companion(): { visible: boolean; label: string; bodies: number; rebuilds: number; pos: { id: string; x: number; y: number }[] } | null {
        const c = companionFor({ mode, session, side, replay })
        if (c === null) return null
        return {
          visible: companionMode !== 'hidden',
          label: c.label,
          bodies: companionEngine === null ? 0 : companionEngine.bodies.size,
          // Reseed count (see companionRebuilds) and live body positions — the
          // e2e diffs these to pin no-reseed on an identity-stable step and the
          // companion's total non-interactivity (a click on it moves nothing).
          rebuilds: companionRebuilds,
          pos: companionEngine === null ? [] : [...companionEngine.bodies.values()].map((b) => ({ id: b.id, x: b.pos.x, y: b.pos.y })),
        }
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
      dispose,
    }
  }

  refreshChrome()
  raf = requestAnimationFrame(frame)

  return { dispose }
}
