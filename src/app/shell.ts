import type { Diagram, NodeId, RegionId, WireId } from '../kernel/diagram/diagram'
import type { DiagramWithBoundary } from '../kernel/diagram/boundary'
import { mkDiagramWithBoundary } from '../kernel/diagram/boundary'
import { parseTerm } from '../kernel/term/parse'
import type { SubgraphSelection } from '../kernel/diagram/subgraph/selection'
import { exploreForm } from '../kernel/diagram/canonical/explore'
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
import { paint, bubbleHues, highlightGroup, LIGHT, THEMES } from '../view/paint'
import { drawShapes } from '../view/canvas'
import { fitCamera } from '../view/camera'
import { seedBodyPlacement } from '../view/placement'
import type { Library } from './library'
import { emptyLibrary, reconcile, loadEntry, unloadEntry, adoptEntry, defineEntry, rebuild } from './library'
import { defineRelation, canonicalArgOrder, inferFoldArgs } from './define'
import type { Replay } from './replay'
import { mkReplay } from './replay'
import { emptyDiagram, addTermNode, addRefNode, addAtomNode } from './edit'
import type { ProofSession, TrackDirection, TrackSession } from './session'
import {
  startSession, applyForward, applyBackward, undoForward, redoForward, undoBackward, redoBackward, meet, assembleTheorem, adoptTheorem, sideBoundary, currentSide,
  startTrack, applyTrack, undoTrack, redoTrack, moveTrack, declareTrack, adoptTrackTheorem, trackBoundary, currentTrack,
} from './session'
import type { Companion } from './companion'
import { companionFor } from './companion'
import { sessionTheory } from './persist'
import { theoryToJson } from '../kernel/proof/store'
import type { Hit } from './hittest'
import { hitTest, wireHitTest, buildSelection } from './hittest'
import { isHitSelected } from './interact/brush'
import { ConstructController } from './interact/construct'
import { SpawnCascade, boundPredicateOptions } from './interact/spawn'
import { ProofMoveController } from './interact/moves'
import { InteractiveViewport, type KeySample, type PointerClaim, type PointerSample } from './interact/viewport'
import { FeedbackController, REFUSAL_LIFETIME_MS, type FeedbackState } from './feedback'
import { mountCompass } from './compass'
import { mountScrubber, type MountedScrubber, type TimelineView } from './interact/scrubber'
import { previewTransition } from './history-preview'
import { FixedSideWorkspace } from './fixed-side-workspace'
import { defaultMotionPreferences, MotionCoordinator, setMotionSpeed } from './interact/motion'
import { ComprehensionEditor } from './comprehension-editor'

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
  | { readonly kind: 'defineRelation'; readonly sel: SubgraphSelection; readonly args: WireId[]; name: string }
  | { readonly kind: 'foldChoose'; readonly sel: SubgraphSelection }

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
  type ActiveProof =
    | { readonly kind: 'track'; track: TrackSession }
    | { readonly kind: 'dual'; session: ProofSession; side: 'forward' | 'backward' }
  let proof: ActiveProof | null = null
  let fixedWorkspace: FixedSideWorkspace | null = null
  let kernelSel: SubgraphSelection | null = null
  let pending: Pending | null = null
  // The render engine is rebuilt whenever the displayed diagram identity
  // changes (layout never persists). Boundary wiring for proof sides is Task 2;
  // an edit sheet has no boundary, so [] is correct here.
  let themeIndex = 0
  let theme: Theme = themeCycle[themeIndex] ?? LIGHT
  const motionPreferences = defaultMotionPreferences(window.matchMedia?.('(prefers-reduced-motion: reduce)').matches ?? false)
  let displayed: Diagram = editDiagram
  let engine: Engine = mkEngine(displayed, [])
  seedProject(engine)
  const mainMotion = new MotionCoordinator({
    preferences: () => motionPreferences,
    diagram: () => displayed,
    engine: () => engine,
    theme: () => theme,
  })
  let interaction!: InteractiveViewport
  let construct!: ConstructController
  let proofMoves!: ProofMoveController
  let comprehensionEditor: ComprehensionEditor | null = null
  let spawnCascade!: SpawnCascade
  let spawnHoverBinder: RegionId | null = null
  const feedback = new FeedbackController()
  let lastPointerClient: Vec2 = { x: window.innerWidth / 2, y: window.innerHeight / 2 }
  let refusalElement: HTMLOutputElement | null = null
  let refusalTimer = 0
  const rememberPointer = (pointer: Vec2): void => {
    lastPointerClient = pointer
    comprehensionEditor?.hostPointerChanged(pointer)
  }
  const clearRefusalPresentation = (sequence?: number): void => {
    feedback.clearRefusal(sequence)
    refusalElement?.remove()
    refusalElement = null
  }
  const refuse = (text: string, pointer: Vec2 = lastPointerClient): void => {
    window.clearTimeout(refusalTimer)
    const refusal = feedback.refuse({ text, pointer })
    refusalElement?.remove()
    const output = document.createElement('output')
    output.className = 'vpa-refusal'
    output.setAttribute('role', 'alert')
    output.setAttribute('aria-live', 'assertive')
    output.value = text
    const left = pointer.x + 334 <= window.innerWidth ? pointer.x + 14 : Math.max(8, pointer.x - 334)
    const top = pointer.y + 72 <= window.innerHeight ? pointer.y + 14 : Math.max(8, pointer.y - 72)
    output.style.cssText = [
      'position:fixed', 'z-index:60', `left:${left}px`, `top:${top}px`, 'max-width:320px',
      'padding:6px 8px', 'border-radius:6px', `border:1px solid ${theme.interaction.refusal}`,
      `background:${theme.paper}`, `color:${theme.interaction.refusal}`, 'font:11px/1.35 system-ui',
      'box-shadow:0 5px 18px rgba(40,20,20,.18)', 'pointer-events:none',
    ].join(';')
    document.body.append(output)
    refusalElement = output
    refusalTimer = window.setTimeout(() => clearRefusalPresentation(refusal.sequence), REFUSAL_LIFETIME_MS)
  }
  const setFeedbackProblem = (problemId: string, text: string): void => {
    feedback.setProblem(problemId, text)
  }
  const clearFeedbackProblem = (problemId: string): void => {
    feedback.clearProblem(problemId)
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
    chrome.dataset.colorMode = theme.name.startsWith('Dark') ? 'dark' : 'light'
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
    if (mode === 'prove' && proof !== null) {
      if (proof.kind === 'track') return currentTrack(proof.track)
      return currentSide(proof.session, proof.side)
    }
    return editDiagram
  }

  // Prove-mode sides render their statement boundary as frame exits; an edit
  // sheet has no boundary. mkEngine ignores boundary ids absent from the
  // current diagram, so a stale id simply draws no exit.
  const currentBoundary = (): readonly WireId[] => {
    if (mode === 'replay' && replay !== null) return replay.boundary
    if (mode === 'prove' && proof !== null) {
      return proof.kind === 'track' ? trackBoundary(proof.track) : sideBoundary(proof.session, proof.side)
    }
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
    b.addEventListener('click', (event) => {
      rememberPointer({ x: event.clientX, y: event.clientY })
      onClick()
    })
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

  const compass = mountCompass(chrome)
  const statusDiv = compass.status
  let temporal: MountedScrubber | null = null
  let historyPreview: HTMLDivElement | null = null
  const previewCache = new WeakMap<Diagram, WeakMap<Diagram, Map<Theme, HTMLCanvasElement>>>()
  const menuDiv = div('vpa-menu')
  menuDiv.id = 'action-menu'
  menuDiv.hidden = true
  menuDiv.setAttribute('role', 'menu')
  let palettePoint: Vec2 | null = null
  const libraryDiv = div('vpa-library')
  libraryDiv.id = 'library'
  compass.libraryBody.append(libraryDiv)

  // ---- Library panel state (browser-only view state) ----
  // The panel opens by default; each per-file detail group and the Session group
  // start collapsed. Load failures are stashed per file name (the empty string
  // keys the "Open file…" picker) and rendered inline, loudly, next to their
  // control. `dirHandle` is the session-lifetime workspace folder (no
  // persistence): opening or refreshing it re-lists its *.json files uniformly.
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

  // Render the Indexed Ledger body from `library`: workspace controls, the uniform
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

  const nameInput = textInput('theorem-name', 'theorem name')
  const fuel = numberInput('fuel-input', 'fuel', 64)

  const guard = (fn: () => void) => (): void => {
    try {
      fn()
    } catch (e) {
      // The kernel's refusal message IS the UX copy — verbatim, with explicit ownership.
      refuse(e instanceof Error ? e.message : String(e))
    }
  }

  const readCount = (input: HTMLInputElement, what: string): number => {
    const n = Number(input.value)
    if (!Number.isInteger(n) || n < 1) throw new Error(`${what} must be a positive integer, got '${input.value}'`)
    return n
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
      const next = mkEngine(d, currentBoundary())
      carryOver(previous, next)
      seedProject(next)
      mainMotion.observeSwap(previous, next, performance.now())
      engine = next
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
    palettePoint = null
    if (mode === 'prove') proofMoves.cancel()
    if (next.length === 0) {
      kernelSel = null
    } else {
      try {
        kernelSel = buildSelection(displayed, next)
      } catch (e) {
        kernelSel = null
        refuse(e instanceof Error ? e.message : String(e))
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
  })
  const onSetRhs = guard(() => {
    requireEdit()
    goalRhs = mkDiagramWithBoundary(editDiagram, [])
  })

  const proofDirection = (): TrackDirection | null => {
    if (proof === null) return null
    return proof.kind === 'track' ? proof.track.direction : proof.side
  }

  const proofStatus = (): string => {
    if (proof === null) return 'no proof'
    if (proof.kind === 'track') return `${proof.track.timeline.cursor} step(s) · declare when ready`
    const session = proof.session
    return `forward ${session.forward.cursor} step(s) · backward ${session.backward.cursor} step(s) · ${meet(session) ? 'fingerprints MET — assemble when ready' : 'not met yet'}`
  }

  // ---- replay stepping ----
  // Open the stepper over a bundled/adopted theorem, remembering the mode we
  // leave so exit restores it. Step 0 (the lhs) seeds a fresh engine.
  const enterReplay = (name: string): void => {
    const thm = ctx.theorems.get(name)
    if (thm === undefined) throw new Error(`unknown theorem '${name}'`)
    if (mode !== 'replay') replayReturnMode = mode
    mainMotion.cancel()
    replay = mkReplay(thm, ctx)
    replayK = 0
    mode = 'replay'
    if (fixedWorkspace !== null) {
      fixedWorkspace.root.hidden = true
      canvas.hidden = false
    }
    compass.setOpen('library', false)
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
    refreshChrome()
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
    refreshChrome()
  }

  const exitReplay = (): void => {
    mode = replayReturnMode
    replay = null
    replayK = 0
    if (mode === 'prove' && proof?.kind === 'dual' && fixedWorkspace !== null) {
      fixedWorkspace.root.hidden = false
      canvas.hidden = true
      refreshChrome()
      return
    }
    sync(true) // rebuilds the engine for the restored mode's diagram
  }

  const leaveProof = guard(() => {
    if (comprehensionEditor !== null || fixedWorkspace?.editing) return
    proofMoves.cancel()
    mainMotion.cancel()
    if (mode === 'replay') {
      exitReplay()
      return
    }
    fixedWorkspace?.dispose()
    fixedWorkspace = null
    proof = null
    mode = 'edit'
    canvas.hidden = false
    sync(true)
  })
  const beginTrack = (direction: TrackDirection): void => guard(() => {
    requireEdit()
    proofMoves.cancel()
    proof = { kind: 'track', track: startTrack(mkDiagramWithBoundary(editDiagram, []), direction, ctx) }
    mode = 'prove'
    sync(true)
  })()
  const beginDual = guard(() => {
    requireEdit()
    proofMoves.cancel()
    if (goalLhs === null || goalRhs === null) throw new Error('set both fixed sides before dual proving')
    const session = startSession(goalLhs, goalRhs, ctx)
    proof = { kind: 'dual', session, side: 'forward' }
    mode = 'prove'
    try {
      fixedWorkspace = new FixedSideWorkspace({
        host: document.body,
        session: () => {
          if (proof?.kind !== 'dual') throw new Error('fixed-side workspace has no active session')
          return proof.session
        },
        commit: (next, changedSide) => {
          if (proof?.kind !== 'dual') throw new Error('fixed-side workspace has no active session')
          proof = { kind: 'dual', session: next, side: changedSide }
        },
        context: () => ctx,
        theme: () => theme,
        motionPreferences: () => motionPreferences,
        fuel: () => readCount(fuel.input, 'fuel'),
        focusChanged: (side) => {
          if (proof?.kind === 'dual') proof = { ...proof, side }
          refreshChrome()
        },
        declare: () => onAssemble(),
        refuse,
        changed: refreshChrome,
      })
    } catch (error) {
      proof = null
      mode = 'edit'
      throw error
    }
    interaction.resetSurface()
    proofMoves.cancel()
    kernelSel = null
    pending = null
    palettePoint = null
    restyleCompanion(false)
    canvas.hidden = true
    refreshChrome()
  })
  const onUndo = guard(() => {
    if (mainMotion.playing || fixedWorkspace?.busy || comprehensionEditor !== null) return
    if (mode === 'edit') {
      const prev = editHistory.pop()
      if (prev === undefined) throw new Error('nothing to undo in edit mode')
      editDiagram = prev
      sync()
      return
    }
    if (mode === 'replay' && replay !== null) {
      if (replayK === 0) throw new Error('nothing to undo in replay')
      gotoReplayStep(replayK - 1)
      return
    }
    if (proof === null) throw new Error('no active proof')
    if (proof.kind === 'track') proof = { kind: 'track', track: undoTrack(proof.track) }
    else {
      proof = { ...proof, session: proof.side === 'forward' ? undoForward(proof.session) : undoBackward(proof.session) }
      fixedWorkspace?.reconcile(proof.side)
      return
    }
    sync()
  })
  const onRedo = guard(() => {
    if (mainMotion.playing || fixedWorkspace?.busy || comprehensionEditor !== null) return
    if (mode === 'replay' && replay !== null) {
      if (replayK === replay.stepCount) throw new Error('nothing to redo in replay')
      gotoReplayStep(replayK + 1)
      return
    }
    if (proof === null) throw new Error('no active proof')
    if (proof.kind === 'track') proof = { kind: 'track', track: redoTrack(proof.track) }
    else {
      proof = { ...proof, session: proof.side === 'forward' ? redoForward(proof.session) : redoBackward(proof.session) }
      fixedWorkspace?.reconcile(proof.side)
      return
    }
    sync()
  })
  const onAssemble = guard(() => {
    if (proof === null) throw new Error('no active proof')
    const name = nameInput.value.trim() === '' ? 'untitled' : nameInput.value.trim()
    const thm = proof.kind === 'track' ? declareTrack(proof.track, name) : assembleTheorem(proof.session, name)
    checkTheorem(thm, ctx)
    // Adopt into the session context (so this session can keep citing it) AND
    // into the library's Session group; applyLibrary rebuilds the merged context
    // and rebinds the shell's live ctx so saves, future citations, and the panel
    // all see the new theorem.
    proof = proof.kind === 'track'
      ? { kind: 'track', track: adoptTrackTheorem(proof.track, thm) }
      : { ...proof, session: adoptTheorem(proof.session, thm) }
    applyLibrary(adoptEntry(library, thm))
  })

  // ---- proof actions ----
  const applyProofStep = (step: ProofStep): void => {
    if (proof === null) throw new Error('no active proof')
    if (proof.kind === 'track') {
      const next = applyTrack(proof.track, step)
      mainMotion.run(step, () => {
        proof = { kind: 'track', track: next }
        sync()
      }, performance.now())
      refreshChrome()
      return
    } else {
      proof = { ...proof, session: proof.side === 'forward' ? applyForward(proof.session, step) : applyBackward(proof.session, step) }
      fixedWorkspace?.reconcile(proof.side)
      return
    }
  }

  const openComprehension = (bubble: RegionId, pointer: Vec2): void => {
    if (mode !== 'prove' || proof?.kind !== 'track' || comprehensionEditor !== null) return
    let editor: ComprehensionEditor
    editor = new ComprehensionEditor({
      mount: document.body,
      canvas,
      diagram: currentDiagram,
      boundary: () => proof?.kind === 'track' ? trackBoundary(proof.track) : [],
      engine: () => engine,
      view: () => view,
      context: () => ctx,
      theme: () => theme,
      fuel: () => readCount(fuel.input, 'fuel'),
      apply: applyProofStep,
      refuse,
      changed: refreshChrome,
      openChanged: (open) => {
        if (!open && comprehensionEditor === editor) comprehensionEditor = null
        refreshChrome()
      },
    }, bubble, pointer)
    comprehensionEditor = editor
    proofMoves.cancel()
    refreshChrome()
  }

  // ---- define relation (EDIT mode, two-phase like relFold) ----
  // Enter the pending pick: the crossing wires clicked in order become the
  // relation's argument boundary. Defining never mutates the sheet.
  const enterDefineRelation = (sel: SubgraphSelection): void => {
    pending = { kind: 'defineRelation', sel, args: [], name: '' }
    refreshChrome()
  }

  // ---- domain pointer claims (selection is owned by InteractiveViewport) ----
  const handleClaimedClick = (sample: PointerSample): void => {
    const hit = hitTest(engine, sample.world, { scale: view.scale })
    if (pending !== null && pending.kind === 'defineRelation') {
      if (hit !== null && hit.kind === 'wire') {
        pending.args.push(hit.id)
        refreshChrome()
      } else {
        refuse('define relation: click wires only (or Commit/Cancel in the palette)', sample.client)
      }
      return
    }
  }

  const claimPointer = (sample: PointerSample): PointerClaim | null => {
    const editorClaim = comprehensionEditor?.hostClaim(sample) ?? null
    const pendingClaim: PointerClaim | null = sample.button === 0 && pending?.kind === 'defineRelation' ? {
        still: 'claim',
        blocksPassiveRelaxation: false,
        move: () => {},
        release: (at, moved) => { if (!moved) handleClaimedClick(at) },
        cancel: () => {},
      } : null
    return editorClaim ?? pendingClaim ?? (mode === 'prove' ? proofMoves.claim(sample) : construct.claim(sample))
  }

  // ---- chrome refresh ----
  const refreshChrome = (): void => {
    const goal = `goal ${goalLhs === null ? 'LHS unset' : 'LHS set'}/${goalRhs === null ? 'RHS unset' : 'RHS set'}`
    if (mode === 'replay' && replay !== null) {
      const rule = replayK === 0 ? '(start)' : replay.labelAt(replayK)
      statusDiv.textContent = `[REPLAY] step ${replayK}/${replay.stepCount} — ${rule}`
    } else {
      const direction = proofDirection()
      const head = mode === 'edit' ? 'EDIT' : `PROVE · ${direction?.toUpperCase() ?? 'UNKNOWN'}`
      statusDiv.textContent = proof?.kind === 'dual'
        ? `[${head} · FIXED SIDES] ${goal} | ${proofStatus()}`
        : `[${head}] ${proofStatus()}`
    }
    compass.setMode(mode === 'edit' ? 'Edit' : mode === 'replay' ? 'Replay' : `Prove ${proofDirection() ?? ''}`.trim())
    backwardBtn.hidden = mode !== 'edit'
    forwardBtn.hidden = mode !== 'edit'
    dualBtn.hidden = mode !== 'edit'
    leaveBtn.hidden = mode === 'edit'
    leaveBtn.textContent = mode === 'replay' ? 'Exit replay' : 'Return to editing'
    nameInput.hidden = mode === 'edit'
    declareBtn.hidden = mode !== 'prove' || proof?.kind === 'dual'
    helpText.textContent = mode === 'edit'
      ? 'Right-click the sheet to construct. Backward proving is the ordinary default; fixed sides use explicit snapshots.'
      : mode === 'replay'
        ? 'Drag the temporal rail or use Arrow keys to inspect the verified derivation.'
        : 'Select diagram structure, then right-click for legal proof moves. Drag the temporal rail to undo or redo.'
    for (const control of motionControls) control.disabled = mainMotion.playing || fixedWorkspace?.busy === true
    temporal?.refresh()

    menuDiv.replaceChildren()
    menuDiv.hidden = true
    if (mode === 'replay' && replay !== null) return
    if (palettePoint === null && pending === null) return
    const point = palettePoint ?? lastPointerClient
    menuDiv.style.position = 'fixed'
    menuDiv.style.left = `${Math.max(8, Math.min(window.innerWidth - 360, point.x + 10))}px`
    menuDiv.style.top = `${Math.max(8, Math.min(window.innerHeight - 280, point.y + 10))}px`
    menuDiv.hidden = false
    if (pending !== null) {
      const p = pending
      const instruction = document.createElement('p')
      instruction.className = 'vpa-action-instruction'
      instruction.textContent = p.kind === 'defineRelation'
        ? `Name the relation; optionally click crossing wires to override canonical order (${p.args.length} picked).`
        : 'Choose the relation whose definition matches the selection.'
      menuDiv.append(instruction)
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
              return
            }
            pending = null
            applyProofStep({ rule: 'relFold', sel: psel, defId: name, args })
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
        })))
      }
      menuDiv.append(button('Cancel pending action', () => {
        pending = null
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
          refreshChrome()
        })))
        if (sel.nodes.length === 1 && sel.regions.length === 0 && sel.wires.length === 0
          && displayed.nodes[sel.nodes[0]!]?.kind === 'ref') {
          menuDiv.append(button('Unfold relation', guard(() => {
            pushEdit(applyRelUnfold(editDiagram, sel.nodes[0]!, ctx.relations))
          })))
        }
      }
      return
    }
    // Proving actions are rendered by ProofMoveController only after an
    // explicit still right-click; the shell retains this palette for EDIT.
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
  const frame = (now = performance.now()): void => {
    if (disposed) return
    if (mode === 'prove' && proof?.kind === 'dual' && fixedWorkspace !== null) {
      canvas.hidden = true
      restyleCompanion(false)
      fixedWorkspace.frame(now)
      raf = requestAnimationFrame(frame)
      return
    }
    canvas.hidden = false
    const comp = companionFor({ mode, replay })
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
    mainMotion.frame(now)
    if (!mainMotion.playing) interaction.advance(comprehensionEditor === null)
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
    const hoverShapes: Shape[] = []
    if (spawnHoverBinder !== null) {
      mainMotion.setHover(`region:${spawnHoverBinder}`, now)
      hoverShapes.push(...highlightGroup(engine, theme, spawnHoverBinder))
    } else {
      const hov = interaction.hover
      mainMotion.setHover(hov === null ? null : `${hov.kind}:${hov.id}`, now)
      if (hov !== null) {
        const binder = hoverGroupBinder(hov)
        if (binder !== null) hoverShapes.push(...highlightGroup(engine, theme, binder))
        else hoverShapes.push(...itemShapes(hov, isHitSelected(interaction.selection, hov) ? theme.interaction.selectedHover : theme.interaction.hover))
      }
    }
    shapes.push(...construct.overlay())
    shapes.push(...proofMoves.overlay())
    if (comprehensionEditor !== null) shapes.push(...comprehensionEditor.hostOverlays())
    ctx2d.clearRect(0, 0, canvas.width, canvas.height)
    ctx2d.fillStyle = theme.canvas
    ctx2d.fillRect(0, 0, canvas.width, canvas.height)
    drawShapes(ctx2d, shapes, view)
    ctx2d.save()
    ctx2d.globalAlpha = mainMotion.hoverFraction(now)
    drawShapes(ctx2d, hoverShapes, view)
    ctx2d.restore()
    drawShapes(ctx2d, mainMotion.overlays(now), view)
    comprehensionEditor?.frame(now)
    renderCompanion(comp, companionVisible)
    raf = requestAnimationFrame(frame)
  }

  // Replay stepping by arrow keys. Inert outside replay mode; ignores keys while
  // a text/number input is focused so typing a term is never hijacked.
  const onKeyDown = (e: KeySample): boolean => {
    if (comprehensionEditor !== null) return true
    if (mode === 'prove' && proof?.kind === 'dual') return false
    if ((e.ctrlKey || e.metaKey) && e.key.toLowerCase() === 'z') {
      if (e.shiftKey) onRedo()
      else onUndo()
      return true
    }
    if (e.key === 'Escape' && spawnCascade.escape()) return true
    if (e.key === 'Escape' && pending !== null) {
      pending = null
      palettePoint = null
      refreshChrome()
      return true
    }
    if (e.key === 'Escape' && palettePoint !== null) {
      palettePoint = null
      refreshChrome()
      return true
    }
    if (proofMoves.keyDown(e)) return true
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
        } catch (e) {
          refuse(e instanceof Error ? e.message : String(e))
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
  const backwardBtn = button('Prove backward', () => beginTrack('backward'))
  const forwardBtn = button('Prove forward', () => beginTrack('forward'))
  const dualBtn = button('Prove fixed sides', beginDual)
  const leaveBtn = button('Return to editing', leaveProof)
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
  const setLhsBtn = button('Set goal LHS', onSetLhs)
  const setRhsBtn = button('Set goal RHS', onSetRhs)
  const declareBtn = button('Declare / assemble + check', onAssemble)
  const helpText = div('vpa-mode-help')
  helpText.hidden = true
  const helpBtn = button('Help', () => { helpText.hidden = !helpText.hidden })
  const keyboardMap = div('vpa-keyboard-map')
  keyboardMap.textContent = 'Ctrl+Z undo · Ctrl+Shift+Z redo · Home fit · Esc cancel · Delete contextual erase'
  keyboardMap.hidden = true
  const keyboardBtn = button('Keyboard map', () => { keyboardMap.hidden = !keyboardMap.hidden })
  const motionGroup = div('vpa-motion-controls')
  const motionCheck = (label: string, className: string, checked: () => boolean, update: (value: boolean) => void): HTMLInputElement => {
    const row = document.createElement('label')
    const input = document.createElement('input')
    input.type = 'checkbox'
    input.className = className
    input.checked = checked()
    input.addEventListener('change', () => update(input.checked))
    row.append(input, label)
    motionGroup.append(row)
    return input
  }
  const conversionMotion = motionCheck('βη animation', 'vpa-motion-conversion', () => motionPreferences.conversionAnimation, (value) => { motionPreferences.conversionAnimation = value })
  const connectedMotion = motionCheck('connected morph (off = pinned v1)', 'vpa-motion-connected', () => motionPreferences.connectedMorph, (value) => { motionPreferences.connectedMorph = value })
  const ghostMotion = motionCheck('transition ghosts', 'vpa-motion-ghosts', () => motionPreferences.transitionGhosts, (value) => { motionPreferences.transitionGhosts = value })
  const hoverMotion = motionCheck('hover ease', 'vpa-motion-hover', () => motionPreferences.hoverEaseMs > 0, (value) => { motionPreferences.hoverEaseMs = value ? 120 : 0 })
  const speedRow = document.createElement('label')
  speedRow.append('speed ')
  const motionSpeed = document.createElement('input')
  motionSpeed.type = 'range'
  motionSpeed.className = 'vpa-motion-speed'
  motionSpeed.min = '0.25'
  motionSpeed.max = '3'
  motionSpeed.step = '0.25'
  motionSpeed.value = String(motionPreferences.speed)
  const motionSpeedValue = document.createElement('output')
  motionSpeedValue.className = 'vpa-motion-speed-value'
  motionSpeedValue.value = `${motionPreferences.speed}×`
  motionSpeed.addEventListener('input', () => {
    setMotionSpeed(motionPreferences, Number(motionSpeed.value))
    motionSpeed.value = String(motionPreferences.speed)
    motionSpeedValue.value = `${motionPreferences.speed}×`
  })
  speedRow.append(motionSpeed, motionSpeedValue)
  motionGroup.prepend(Object.assign(document.createElement('b'), { textContent: 'Motion' }))
  motionGroup.append(speedRow)
  const motionControls = [conversionMotion, connectedMotion, ghostMotion, hoverMotion, motionSpeed]
  compass.lifecycle.append(backwardBtn, forwardBtn, setLhsBtn, setRhsBtn, dualBtn, leaveBtn, nameInput, declareBtn, helpBtn, helpText)
  compass.utilities.append(
    themeBtn,
    companionBtn,
    fuel.wrap,
    button('Open folder…', onOpenFolder),
    button('Open file…', () => openFileInput.click()),
    button('Save theory', onSave),
    keyboardBtn,
    keyboardMap,
    motionGroup,
  )
  chrome.append(menuDiv, openFileInput)
  spawnCascade = new SpawnCascade({
    host: document.body,
    spawnTerm: ({ source, invocation }) => {
      try {
        const added = addTermNode(editDiagram, invocation.region, parseTerm(source))
        pushEdit(added.diagram, { node: added.node, at: invocation.world }, true)
        return true
      } catch (error) {
        refuse(error instanceof Error ? error.message : String(error), invocation.screen)
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
        return true
      } catch (error) {
        refuse(error instanceof Error ? error.message : String(error), invocation.screen)
        return false
      }
    },
    spawnBoundPredicate: ({ binder, invocation }) => {
      try {
        const added = addAtomNode(editDiagram, invocation.region, binder)
        pushEdit(added.diagram, { node: added.node, at: invocation.world }, true)
        return true
      } catch (error) {
        refuse(error instanceof Error ? error.message : String(error), invocation.screen)
        return false
      }
    },
    binderColor: (binder) => {
      const color = bubbleHues(editDiagram, theme.bubbleLightness).get(binder)
      if (color === undefined) throw new Error(`bound-predicate option references missing bubble '${binder}'`)
      return color
    },
    hoverBinder: (binder) => { spawnHoverBinder = binder },
  })
  construct = new ConstructController({
    host: document.body,
    active: () => mode === 'edit' && !mainMotion.playing,
    engine: () => engine,
    viewScale: () => view.scale,
    diagram: () => editDiagram,
    selection: () => interaction.selection,
    setSelection: (selection) => interaction.setSelection(selection),
    commit: (diagram) => pushEdit(diagram),
    refuse,
    setProblem: setFeedbackProblem,
    clearProblem: clearFeedbackProblem,
    openSpawn: (sample, region) => {
      if (isHitSelected(interaction.selection, sample.hit)) {
        palettePoint = sample.client
        refreshChrome()
      } else {
        spawnCascade.open(
          { screen: sample.client, world: sample.world, region },
          ctx.relations,
          boundPredicateOptions(editDiagram, region),
        )
      }
    },
    theme: () => theme,
  })
  proofMoves = new ProofMoveController({
    host: document.body,
    active: () => mode === 'prove' && proof?.kind === 'track' && !mainMotion.playing && comprehensionEditor === null,
    diagram: currentDiagram,
    engine: () => engine,
    viewScale: () => view.scale,
    selection: () => interaction.selection,
    setSelection: (selection) => interaction.setSelection(selection),
    context: () => ctx,
    orientation: () => proofDirection() ?? 'forward',
    apply: applyProofStep,
    refuse: (text, pointer) => refuse(text, pointer),
    theme: () => theme,
    fuel: () => readCount(fuel.input, 'fuel'),
    openComprehension,
  })
  interaction = new InteractiveViewport({
    canvas,
    view,
    engine: () => engine,
    diagram: () => displayed,
    selectionEnabled: () => mode !== 'replay',
    claim: claimPointer,
    doubleClick: (sample) => comprehensionEditor !== null ? false : mode === 'prove' && proofMoves.doubleClick(sample),
    contextMenu: (sample) => {
      if (mode === 'prove') {
        if (comprehensionEditor !== null) return
        proofMoves.contextMenu(sample)
        return
      }
      if (!isHitSelected(interaction.selection, sample.hit)) return
      palettePoint = sample.client
      refreshChrome()
    },
    pointerChanged: rememberPointer,
    keyDown: onKeyDown,
    selectionChanged,
    selectionCommitted: () => {
      pending = null
      refreshChrome()
    },
    inputAllowed: () => !mainMotion.playing,
  })
  const timelineView = (): TimelineView | null => {
    if (mode === 'replay' && replay !== null) {
      return {
        states: Array.from({ length: replay.stepCount + 1 }, (_, cursor) => replay!.diagramAt(cursor)),
        transitions: replay.steps,
        cursor: replayK,
        boundary: replay.boundary,
        inputAllowed: () => true,
        moveTo: gotoReplayStep,
      }
    }
    if (mode !== 'prove' || proof === null) return null
    if (proof.kind === 'track') {
      const active = proof.track
      return {
        ...active.timeline,
        boundary: trackBoundary(active),
        inputAllowed: () => !mainMotion.playing && comprehensionEditor === null,
        moveTo: (cursor) => {
          if (proof?.kind !== 'track') return
          proof = { kind: 'track', track: moveTrack(proof.track, cursor) }
          sync()
        },
      }
    }
    const activeProof = proof
    const active = activeProof.session[activeProof.side]
    return {
      ...active,
      name: activeProof.side,
      boundary: sideBoundary(activeProof.session, activeProof.side),
      inputAllowed: () => fixedWorkspace?.busy !== true,
      moveTo: (cursor) => {
        fixedWorkspace?.moveFocusedCursor(cursor)
      },
    }
  }
  const closeHistoryPreview = (): void => {
    historyPreview?.remove()
    historyPreview = null
  }
  const renderHistoryPreview = (cursor: number, anchor: { readonly x: number; readonly y: number }): void => {
    const timeline = timelineView()
    if (timeline === null) return
    const transition = previewTransition(timeline.states, cursor)
    let byAfter = previewCache.get(transition.before)
    if (byAfter === undefined) {
      byAfter = new WeakMap()
      previewCache.set(transition.before, byAfter)
    }
    let byTheme = byAfter.get(transition.after)
    if (byTheme === undefined) {
      byTheme = new Map()
      byAfter.set(transition.after, byTheme)
    }
    let previewCanvas = byTheme.get(theme)
    if (previewCanvas === undefined) {
      previewCanvas = document.createElement('canvas')
      previewCanvas.width = 520
      previewCanvas.height = 340
      const previewContext = previewCanvas.getContext('2d')
      if (previewContext === null) return
      const previewEngine = mkEngine(transition.after, timeline.boundary)
      seedProject(previewEngine)
      for (let i = 0; i < 16; i++) settleStep(previewEngine, null)
      const points: Vec2[] = []
      if (transition.focus.kind === 'items') {
        for (const id of transition.focus.nodes) {
          const body = previewEngine.bodies.get(id)
          if (body !== undefined) points.push(body.pos)
        }
        for (const id of transition.focus.wires) {
          const hub = previewEngine.bodies.get(`j:${id}`)
          if (hub !== undefined) points.push(hub.pos)
          for (const endpoint of transition.after.wires[id]?.endpoints ?? []) {
            const body = previewEngine.bodies.get(endpoint.node)
            if (body !== undefined) points.push(body.pos)
          }
        }
      }
      const previewView = points.length === 0
        ? fitCamera(previewEngine.frame === null ? undefined : { center: previewEngine.frame.center, radius: previewEngine.frame.half }, previewCanvas.width, previewCanvas.height, 1)
        : (() => {
            const minX = Math.min(...points.map((point) => point.x))
            const maxX = Math.max(...points.map((point) => point.x))
            const minY = Math.min(...points.map((point) => point.y))
            const maxY = Math.max(...points.map((point) => point.y))
            const scale = Math.min(previewCanvas!.width / Math.max(80, maxX - minX + 80), previewCanvas!.height / Math.max(80, maxY - minY + 80))
            return { scale, offsetX: previewCanvas!.width / 2 - (minX + maxX) / 2 * scale, offsetY: previewCanvas!.height / 2 - (minY + maxY) / 2 * scale }
          })()
      previewContext.fillStyle = theme.canvas
      previewContext.fillRect(0, 0, previewCanvas.width, previewCanvas.height)
      drawShapes(previewContext, paint(previewEngine, theme), previewView)
      byTheme.set(theme, previewCanvas)
    }
    closeHistoryPreview()
    const popup = document.createElement('div')
    popup.className = 'vpa-history-preview'
    popup.style.left = `${Math.max(8, Math.min(window.innerWidth - 282, anchor.x - 130))}px`
    popup.style.top = `${Math.max(8, anchor.y - 194)}px`
    popup.append(previewCanvas)
    document.body.append(popup)
    historyPreview = popup
  }
  temporal = mountScrubber(compass.temporalHost, timelineView, {
    preview: renderHistoryPreview,
    closePreview: closeHistoryPreview,
    unavailable: (command) => refuse(`nothing to ${command}`),
  })
  const closePaletteAfterAction = (event: MouseEvent): void => {
    if (!(event.target instanceof HTMLButtonElement)) return
    queueMicrotask(() => {
      if (pending !== null) return
      palettePoint = null
      refreshChrome()
    })
  }
  const closePaletteOutside = (event: MouseEvent): void => {
    if (palettePoint === null || pending !== null || menuDiv.contains(event.target as Node)) return
    palettePoint = null
    refreshChrome()
  }
  menuDiv.addEventListener('click', closePaletteAfterAction)
  document.addEventListener('click', closePaletteOutside, true)
  renderLibrary()

  const dispose = (): void => {
    if (disposed) return
    disposed = true
    cancelAnimationFrame(raf)
    interaction.dispose()
    construct.dispose()
    spawnCascade.dispose()
    proofMoves.dispose()
    comprehensionEditor?.dispose()
    comprehensionEditor = null
    mainMotion.dispose()
    fixedWorkspace?.dispose()
    fixedWorkspace = null
    temporal?.dispose()
    temporal = null
    window.clearTimeout(refusalTimer)
    clearRefusalPresentation()
    menuDiv.removeEventListener('click', closePaletteAfterAction)
    document.removeEventListener('click', closePaletteOutside, true)
    compass.dispose()
    companionWrap.remove()
    if ((window as any).__vpaDebug !== undefined) delete (window as any).__vpaDebug
  }

  // ---- E2E debug seam: window.__vpaDebug hook when ?debug in URL ----
  if (new URLSearchParams(location.search).has('debug')) {
    ;(window as any).__vpaDebug = {
      nodeCount(): number {
        return Object.keys(currentDiagram().nodes).length
      },
      status(): string {
        return statusDiv.textContent ?? ''
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
      proof(): null | { kind: 'track'; direction: TrackDirection } | { kind: 'dual'; side: 'forward' | 'backward' } {
        if (proof === null) return null
        return proof.kind === 'track'
          ? { kind: 'track', direction: proof.track.direction }
          : { kind: 'dual', side: proof.side }
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
      fixed() {
        return fixedWorkspace?.debugState() ?? null
      },
      motion() {
        return { ...mainMotion.debugState(performance.now()), preferences: { ...motionPreferences } }
      },
      comprehension() {
        return comprehensionEditor?.debugState() ?? null
      },
      spawnBinderHover(): string | null {
        return spawnHoverBinder
      },
      bodies(): { id: string; kind: string; x: number; y: number; r: number; region: string }[] {
        return [...engine.bodies.values()].map((b) => ({ id: b.id, kind: b.kind, x: b.pos.x, y: b.pos.y, r: b.discR, region: b.region }))
      },
      diagram(): {
        nodes: { id: string; kind: string; region: string; defId: string | null; binder: string | null }[]
        wires: { id: string; scope: string; endpoints: number }[]
        regions: { id: string; kind: string; parent: string | null }[]
      } {
        return {
          nodes: Object.entries(displayed.nodes).map(([id, node]) => ({
            id,
            kind: node.kind,
            region: node.region,
            defId: node.kind === 'ref' ? node.defId : null,
            binder: node.kind === 'atom' ? node.binder : null,
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
        const c = companionFor({ mode, replay })
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
