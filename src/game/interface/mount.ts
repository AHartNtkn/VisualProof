import { polarity } from '../../kernel/diagram/regions'
import type { ProofStep } from '../../kernel/proof/step'
import { DARK } from '../../view/paint'
import type { Vec2 } from '../../view/vec'
import { artifactTheoremContext } from '../artifact-theorem'
import type { GameCatalog } from '../catalog'
import { openingCatalog } from '../content'
import type {
  GameControllerState,
} from '../controller-state'
import {
  reduceGame,
  type GameAction,
  type GameEffect,
} from '../controller'
import type { CursebreakerPlatform } from '../platform'
import { decodeGameSave, encodeGameSave } from '../save'
import { currentDiagram, type GameSession } from '../session'
import {
  EMPTY_ARCHIVE_SUBSTRATE_SEED,
  puzzleSubstrateSeed,
} from './substrate-presentation'
import { mountLensEnvironment, type MountedLensEnvironment } from './lens-environment'
import { mountFolioView, type MountedFolioView } from './folio-view'
import { projectFolio } from './folio-projection'
import { gameProofMotionPreferences } from './proof-motion'
import { GameProofViewport, type GameProofViewportDebug } from './proof-surface'
import { mountTimelineLever, type MountedTimelineLever } from './timeline-lever'
import {
  mountGamePresentationView,
  type GamePresentationProjection,
  type MountedGamePresentationView,
} from './game-presentation-view'

const REFUSAL_LIFETIME_MS = 1_800

export class CursebreakerLaunchError extends Error {
  override readonly name = 'CursebreakerLaunchError'
}

export type CursebreakerPresentationProjection = GamePresentationProjection

export type CursebreakerMountOptions = {
  readonly host: HTMLElement
  readonly platform: CursebreakerPlatform
  readonly catalog?: GameCatalog
}

export type CursebreakerRect = {
  readonly left: number
  readonly top: number
  readonly width: number
  readonly height: number
}

export type CursebreakerDebugState = {
  readonly state: GameControllerState
  readonly substrateSeed: string
  readonly proof: GameProofViewportDebug | null
  readonly timeline: { readonly cursor: number; readonly count: number } | null
  readonly proofInstance: number | null
  readonly proofRegions: readonly {
    readonly id: string
    readonly kind: string
    readonly client: Vec2
    readonly interiorClient: Vec2
    readonly rimClient: Vec2
    readonly polarity: 'positive' | 'negative'
  }[]
  readonly proofNodes: readonly {
    readonly id: string
    readonly kind: string
    readonly client: Vec2
  }[]
  readonly layout: {
    readonly kind: string | undefined
    readonly folioPresentation: string | undefined
    readonly lens: CursebreakerRect
  }
  readonly presentation: CursebreakerPresentationProjection
  readonly saveFailure: string | null
}

export type MountedCursebreaker = {
  dispatch(action: GameAction): void
  settled(): Promise<void>
  dispose(): void
  debug(): CursebreakerDebugState
  canvasToClient(worldPoint: Vec2): Vec2
}

const rectSnapshot = (element: Element): CursebreakerRect => {
  const rect = element.getBoundingClientRect()
  return { left: rect.left, top: rect.top, width: rect.width, height: rect.height }
}

const sameSession = (left: GameSession | null, right: GameSession | null): boolean =>
  left === right

const errorText = (error: unknown): string => error instanceof Error ? error.message : String(error)

const proofInputAllowedFor = (state: GameControllerState): boolean => {
  if (state.mode !== 'puzzle') return false
  const transient = state.transient
  return transient === null
    || transient.kind === 'editor'
}

/** Sole mutable renderer owner for the production Cursebreaker game. */
export class CursebreakerRuntime implements MountedCursebreaker {
  readonly #host: HTMLElement
  readonly #window: Window & typeof globalThis
  readonly #catalog: GameCatalog
  readonly #platform: CursebreakerPlatform
  readonly #environment: MountedLensEnvironment
  readonly #presentation: MountedGamePresentationView
  #state: GameControllerState
  #folio: MountedFolioView | null = null
  #proof: GameProofViewport | null = null
  readonly #timeline: MountedTimelineLever
  #proofResize: ResizeObserver | null = null
  #frameRequest: number | null = null
  #proofInstance = 0
  #activeProofInstance: number | null = null
  #refusal: HTMLOutputElement | null = null
  #refusalTimer: number | null = null
  #writeQueue: Promise<void> = Promise.resolve()
  #effectQueue: Promise<void> = Promise.resolve()
  #saveFailure: unknown = null
  #latestSave: unknown
  #removeExitListener: () => void
  #exitQueued = false
  #disposed = false

  constructor(options: {
    readonly host: HTMLElement
    readonly platform: CursebreakerPlatform
    readonly catalog: GameCatalog
    readonly state: GameControllerState
  }) {
    this.#host = options.host
    this.#catalog = options.catalog
    this.#platform = options.platform
    this.#state = options.state
    this.#latestSave = encodeGameSave(this.#catalog, this.#state)
    const runtimeWindow = options.host.ownerDocument.defaultView
    if (runtimeWindow === null) throw new Error('Cursebreaker must mount in a live window')
    this.#window = runtimeWindow

    options.host.replaceChildren()
    this.#environment = mountLensEnvironment({
      host: options.host,
      substrateSeed: this.#substrateSeed(this.#state),
      width: runtimeWindow.innerWidth,
      height: runtimeWindow.innerHeight,
      folioDrawerInputAllowed: () => this.#folioInputAllowed(),
    })
    this.#timeline = mountTimelineLever(
      this.#environment.timelineHandleSlot,
      this.#timelineProjection(this.#state),
      (cursor) => this.dispatch({ kind: 'moveTimeline', cursor }),
      () => this.#timelineInputAllowed(),
    )
    this.#presentation = mountGamePresentationView({
      host: this.#environment.presentationHost,
      projection: this.#presentationProjection(this.#state),
      dispatch: (action) => this.dispatch(action),
    })
    this.#reconcileRoot()
    this.#mountFolio()
    if (this.#state.mode === 'puzzle') this.#mountPuzzle()

    this.#window.addEventListener('resize', this.#onResize)
    this.#window.addEventListener('keydown', this.#onKeyDown)
    this.#removeExitListener = this.#platform.onExitRequested(() => this.#queueExit())
  }

  dispatch(action: GameAction): void {
    if (this.#disposed || this.#exitQueued) return
    const previous = this.#state
    const transition = reduceGame(this.#catalog, previous, action)
    if (transition.state !== previous) {
      this.#commitState(previous, transition.state, false, action.kind === 'setCultureScroll')
    }
    for (const effect of transition.effects) this.#queueEffect(effect)
  }

  async settled(): Promise<void> {
    await this.#effectQueue
    await this.#writeQueue
    if (this.#saveFailure !== null) throw this.#saveFailure
  }

  dispose(): void {
    if (this.#disposed) return
    this.#disposed = true
    this.#removeExitListener()
    this.#window.removeEventListener('resize', this.#onResize)
    this.#window.removeEventListener('keydown', this.#onKeyDown)
    this.#disposePuzzle()
    this.#timeline.dispose()
    this.#folio?.dispose()
    this.#folio = null
    this.#clearRefusal()
    this.#presentation.dispose()
    this.#environment.dispose()
  }

  debug(): CursebreakerDebugState {
    const session = this.#activeSession(this.#state)
    const diagram = session === null ? null : currentDiagram(session)
    const proofRegions = this.#proof === null || diagram === null ? [] : [...this.#proof.engine.regions]
      .map(([id, geometry]) => ({
        id,
        kind: diagram.regions[id]?.kind ?? 'unknown',
        client: this.canvasToClient(geometry.center),
        interiorClient: this.canvasToClient({
          x: geometry.center.x + geometry.radius * 0.72,
          y: geometry.center.y,
        }),
        rimClient: this.canvasToClient({
          x: geometry.center.x + geometry.radius * 0.96,
          y: geometry.center.y,
        }),
        polarity: polarity(diagram, id),
      }))
    const proofNodes = this.#proof === null || diagram === null ? [] : [...this.#proof.engine.bodies]
      .flatMap(([id, body]) => body.node === null ? [] : [{
        id,
        kind: diagram.nodes[id]?.kind ?? 'unknown',
        client: this.canvasToClient(body.pos),
      }])
    return {
      state: this.#state,
      substrateSeed: this.#substrateSeed(this.#state),
      proof: this.#proof?.debug() ?? null,
      timeline: session === null ? null : {
        cursor: session.timeline.cursor,
        count: session.timeline.states.length,
      },
      proofInstance: this.#activeProofInstance,
      proofRegions,
      proofNodes,
      layout: {
        kind: this.#environment.element.dataset.layout,
        folioPresentation: this.#environment.element.dataset.folioPresentation,
        lens: rectSnapshot(this.#environment.proofCanvasSlot.parentElement!),
      },
      presentation: this.#presentationProjection(this.#state),
      saveFailure: this.#saveFailure === null ? null : errorText(this.#saveFailure),
    }
  }

  canvasToClient(worldPoint: Vec2): Vec2 {
    const proof = this.#proof
    if (proof === null) throw new Error('there is no active proof canvas')
    const rect = proof.canvas.getBoundingClientRect()
    return {
      x: rect.left + (worldPoint.x * proof.view.scale + proof.view.offsetX)
        * rect.width / proof.canvas.width,
      y: rect.top + (worldPoint.y * proof.view.scale + proof.view.offsetY)
        * rect.height / proof.canvas.height,
    }
  }

  #activeSession(state: GameControllerState): GameSession | null {
    if (state.mode !== 'puzzle' || state.activePuzzle === null) return null
    return (state.completed.has(state.activePuzzle)
      ? state.replays
      : state.firstAttempts).get(state.activePuzzle) ?? null
  }

  #substrateSeed(state: GameControllerState): string {
    return state.activePuzzle === null
      ? EMPTY_ARCHIVE_SUBSTRATE_SEED
      : puzzleSubstrateSeed(this.#catalog, state.activePuzzle)
  }

  #commitState(
    previous: GameControllerState,
    next: GameControllerState,
    proofWillReconcile: boolean,
    keepLiveFolio = false,
  ): void {
    this.#state = next
    this.#latestSave = encodeGameSave(this.#catalog, next)
    this.#reconcile(previous, next, proofWillReconcile, keepLiveFolio)
    this.#enqueueSave(this.#latestSave)
  }

  #commitPreparedStep(
    preparedFrom: GameControllerState,
    prepared: ReturnType<typeof reduceGame>,
  ): void {
    if (this.#disposed || this.#exitQueued) return
    const current = this.#state
    if (
      current.mode !== preparedFrom.mode
      || current.activePuzzle !== preparedFrom.activePuzzle
      || this.#activeSession(current) !== this.#activeSession(preparedFrom)
    ) return
    const authoritative = prepared.state
    const next: GameControllerState = {
      ...current,
      mode: authoritative.mode,
      activePuzzle: authoritative.activePuzzle,
      completed: authoritative.completed,
      firstAttempts: authoritative.firstAttempts,
      replays: authoritative.replays,
      deliveredGuidance: authoritative.deliveredGuidance,
      guidance: authoritative.guidance,
      completionReceipt: authoritative.completionReceipt,
      transient: authoritative.mode === 'completion' ? null : current.transient,
    }
    this.#commitState(current, next, true)
    for (const effect of prepared.effects) this.#queueEffect(effect)
  }

  #reconcile(
    previous: GameControllerState,
    next: GameControllerState,
    proofWillReconcile: boolean,
    keepLiveFolio: boolean,
  ): void {
    if (proofInputAllowedFor(previous) && !proofInputAllowedFor(next)) {
      this.#proof?.cancelActiveGesture()
    }
    this.#reconcileRoot()
    this.#environment.setSubstrateSeed(this.#substrateSeed(next))
    this.#presentation.update(this.#presentationProjection(next))
    this.#timeline.update(this.#timelineProjection(next))

    if (previous.mode !== next.mode && next.mode === 'archive') {
      this.#environment.setFolioDrawerOpen(true)
    } else if (previous.mode === 'archive' && next.mode === 'puzzle') {
      this.#environment.setFolioDrawerOpen(false)
    }

    const previousPuzzle = previous.mode === 'puzzle' ? previous.activePuzzle : null
    const nextPuzzle = next.mode === 'puzzle' ? next.activePuzzle : null
    if (previousPuzzle !== nextPuzzle) {
      this.#disposePuzzle()
      if (nextPuzzle !== null) this.#mountPuzzle()
    } else if (nextPuzzle !== null) {
      const previousSession = this.#activeSession(previous)
      const nextSession = this.#activeSession(next)
      if (!proofWillReconcile && !sameSession(previousSession, nextSession)) {
        this.#proof?.reconcileDiagram()
      }
      this.#proof?.setReducedMotion(next.settings.reducedMotion)
    }

    const previousHasFolio = previous.mode === 'archive' || previous.mode === 'puzzle'
    const nextHasFolio = next.mode === 'archive' || next.mode === 'puzzle'
    if (previousHasFolio && !nextHasFolio) {
      this.#folio?.dispose()
      this.#folio = null
    } else if (!previousHasFolio && nextHasFolio) {
      this.#mountFolio()
    } else if (nextHasFolio && !keepLiveFolio) {
      this.#folio?.update(projectFolio(this.#catalog, next, next.mode as 'archive' | 'puzzle'))
    }
  }

  #reconcileRoot(): void {
    const root = this.#environment.element
    root.dataset.mode = this.#state.mode
    root.dataset.textSize = this.#state.settings.textSize
    root.dataset.reducedMotion = String(this.#state.settings.reducedMotion)
  }

  #mountFolio(): void {
    if (this.#folio !== null || this.#state.mode === 'completion') return
    this.#folio = mountFolioView({
      host: this.#environment.folioHost,
      projection: projectFolio(this.#catalog, this.#state, this.#state.mode),
      inputAllowed: () => this.#folioInputAllowed(),
      onSelectPuzzle: (puzzle) => this.dispatch({ kind: 'selectPuzzle', puzzle }),
      onRefusePuzzle: (puzzle) => this.dispatch({ kind: 'selectPuzzle', puzzle }),
      onSelectCulture: (culture) => this.dispatch({ kind: 'selectCulture', culture }),
      onRefuseCulture: (culture) => this.dispatch({ kind: 'selectCulture', culture }),
      onScroll: (culture, scroll) => {
        if ((this.#state.scrollByCulture.get(culture) ?? 0) !== scroll) {
          this.dispatch({ kind: 'setCultureScroll', culture, scroll })
        }
      },
      onTheoremDragStart: () => {},
      onTheoremDragMove: () => {},
      onTheoremDragEnd: (puzzle, sample) => {
        this.#proof?.dropArtifact(this.#catalog.puzzle(puzzle), {
          x: sample.clientX,
          y: sample.clientY,
        })
      },
      onTheoremDragCancel: () => {},
    })
  }

  #presentationProjection(state: GameControllerState): CursebreakerPresentationProjection {
    const receipt = state.completionReceipt
    const completion = receipt === null ? null : (() => {
      const puzzle = this.#catalog.puzzle(receipt.puzzle)
      const authored = puzzle.teacher.find(({ trigger }) => trigger.kind === 'completion')?.pages[0]
      return {
        receipt,
        artifactName: puzzle.name.professional,
        response: authored ?? puzzle.provenance.function,
      }
    })()
    return {
      mode: state.mode,
      transient: state.transient,
      guidance: state.guidance,
      settings: state.settings,
      completion,
    }
  }

  #timelineProjection(state: GameControllerState): Parameters<MountedTimelineLever['update']>[0] {
    const session = this.#activeSession(state)
    if (session !== null) return { kind: 'active', timeline: session.timeline }
    if (state.mode === 'completion' && state.completionReceipt !== null) {
      return {
        kind: 'inactive',
        position: 'complete',
        moves: state.completionReceipt.moves,
      }
    }
    return { kind: 'inactive', position: 'home', moves: 0 }
  }

  #mountPuzzle(): void {
    const puzzle = this.#state.activePuzzle === null
      ? null
      : this.#catalog.puzzle(this.#state.activePuzzle)
    if (puzzle === null) return
    this.#proofInstance += 1
    this.#activeProofInstance = this.#proofInstance
    this.#proof = new GameProofViewport({
      host: this.#environment.proofCanvasSlot,
      overlayHost: this.#environment.element,
      diagram: () => currentDiagram(this.#requireActiveSession()),
      boundary: () => puzzle.goal.boundary,
      context: () => artifactTheoremContext(
        this.#catalog.source.puzzles,
        this.#state.completed,
        this.#catalog.source.context,
      ),
      orientation: () => 'backward',
      theme: () => DARK,
      fuel: () => 256,
      prepare: (step: ProofStep) => {
        const preparedFrom = this.#state
        const prepared = reduceGame(this.#catalog, preparedFrom, {
          kind: 'applyStep', step,
        })
        return () => this.#commitPreparedStep(preparedFrom, prepared)
      },
      motionPreferences: () => gameProofMotionPreferences(this.#state.settings.reducedMotion),
      inputAllowed: () => this.#proofInputAllowed(),
      refuse: (text, pointer) => this.#presentRefusal(text, pointer),
      changed: () => {},
      constructionChanged: (open) => this.dispatch({ kind: open ? 'openEditor' : 'closeEditor' }),
    })
    this.#proofResize = new this.#window.ResizeObserver((entries) => {
      const entry = entries.find(({ target }) => target === this.#environment.proofCanvasSlot)
      if (entry !== undefined) this.#proof?.resize(entry.contentRect.width, entry.contentRect.height)
    })
    this.#proofResize.observe(this.#environment.proofCanvasSlot)
    const rect = this.#environment.proofCanvasSlot.getBoundingClientRect()
    this.#proof.resize(rect.width, rect.height)
    const animate = (now: number): void => {
      const owned = this.#proof
      if (owned === null || this.#disposed) return
      owned.frame(now)
      if (this.#proof !== owned || this.#disposed) return
      this.#frameRequest = this.#window.requestAnimationFrame(animate)
    }
    this.#frameRequest = this.#window.requestAnimationFrame(animate)
  }

  #disposePuzzle(): void {
    if (this.#frameRequest !== null) this.#window.cancelAnimationFrame(this.#frameRequest)
    this.#frameRequest = null
    this.#proofResize?.disconnect()
    this.#proofResize = null
    this.#proof?.dispose()
    this.#proof = null
    this.#activeProofInstance = null
  }

  #requireActiveSession(): GameSession {
    const session = this.#activeSession(this.#state)
    if (session === null) throw new Error('the controller has no active puzzle session')
    return session
  }

  #proofInputAllowed(): boolean {
    return proofInputAllowedFor(this.#state)
  }

  #timelineInputAllowed(): boolean {
    return this.#proofInputAllowed()
      && !(this.#proof?.editing ?? false)
      && !(this.#proof?.playing ?? false)
  }

  #folioInputAllowed(): boolean {
    return this.#state.transient === null
  }

  #enqueueSave(document: unknown): void {
    const queued = this.#writeQueue.then(() => this.#platform.writeSave(document))
    this.#writeQueue = queued
    void queued.catch((error: unknown) => {
      if (this.#saveFailure === null) this.#saveFailure = error
    })
  }

  #queueEffect(effect: GameEffect): void {
    if (effect.kind === 'selectionRefused') {
      this.#folio?.resistPuzzle(effect.puzzle)
      return
    }
    if (effect.kind === 'cultureSelectionRefused') {
      this.#folio?.resistCulture(effect.culture)
      return
    }
    if (effect.kind === 'saveBeforeExitAndExitRequested') {
      this.#queueExit()
      return
    }
    const queued = this.#effectQueue.then(async () => {
      if (this.#disposed) return
      const fullscreen = await this.#platform.setFullscreen(effect.fullscreen)
      if (this.#disposed) return
      if (fullscreen === this.#state.settings.fullscreen) return
      const previous = this.#state
      const next = {
        ...previous,
        settings: { ...previous.settings, fullscreen },
      }
      this.#commitState(previous, next, false)
    })
    this.#effectQueue = queued
    void queued.catch((error: unknown) => {
      if (this.#saveFailure === null) this.#saveFailure = error
    })
  }

  #queueExit(): void {
    if (this.#disposed || this.#exitQueued) return
    this.#exitQueued = true
    const queued = this.#effectQueue.then(async () => {
      await this.#writeQueue
      await this.#platform.requestExit(this.#latestSave)
    })
    this.#effectQueue = queued
    void queued.catch((error: unknown) => {
      if (this.#saveFailure === null) this.#saveFailure = error
    })
  }

  #presentRefusal(text: string, pointer: Vec2): void {
    this.#clearRefusal()
    const output = this.#host.ownerDocument.createElement('output')
    output.className = 'curse-refusal'
    output.setAttribute('role', 'alert')
    output.textContent = text
    output.style.left = `${pointer.x + 12}px`
    output.style.top = `${pointer.y + 12}px`
    this.#host.ownerDocument.body.append(output)
    this.#refusal = output
    this.#refusalTimer = this.#window.setTimeout(this.#clearRefusal, REFUSAL_LIFETIME_MS)
  }

  #clearRefusal = (): void => {
    this.#refusal?.remove()
    this.#refusal = null
    if (this.#refusalTimer !== null) this.#window.clearTimeout(this.#refusalTimer)
    this.#refusalTimer = null
  }

  #onResize = (): void => {
    if (this.#disposed) return
    this.#environment.setLayout(this.#window.innerWidth, this.#window.innerHeight)
  }

  #onKeyDown = (event: KeyboardEvent): void => {
    if (this.#disposed || event.repeat) return
    if (this.#proof?.editing) return
    if ((this.#proof?.playing ?? false) && event.key !== 'Escape') return
    if (event.defaultPrevented) return
    const target = event.target
    if (target instanceof this.#window.HTMLInputElement
      || target instanceof this.#window.HTMLTextAreaElement
      || (target instanceof this.#window.HTMLElement && target.isContentEditable)) return
    if (event.key === 'Escape') {
      event.preventDefault()
      this.dispatch({ kind: 'escape' })
      return
    }
    if (
      event.altKey
      || (!event.ctrlKey && !event.metaKey)
      || event.key.toLowerCase() !== 'z'
      || this.#state.transient !== null
      || this.#state.mode !== 'puzzle'
    ) return
    const active = this.#host.ownerDocument.activeElement
    if (active !== this.#host.ownerDocument.body && active !== this.#proof?.canvas) return
    const session = this.#activeSession(this.#state)
    if (session === null) return
    const cursor = session.timeline.cursor + (event.shiftKey ? 1 : -1)
    if (cursor < 0 || cursor >= session.timeline.states.length) return
    event.preventDefault()
    this.dispatch({ kind: 'moveTimeline', cursor })
  }
}

export async function mountCursebreaker(
  options: CursebreakerMountOptions,
): Promise<MountedCursebreaker> {
  const catalog = options.catalog ?? openingCatalog()
  let saved: unknown | null
  try {
    saved = await options.platform.loadSave()
  } catch (error) {
    throw new CursebreakerLaunchError(`Could not load the game save: ${errorText(error)}`)
  }
  let state: GameControllerState
  try {
    state = saved === null
      ? (await import('../controller-state')).createInitialGameState(catalog, {
        reducedMotion: options.host.ownerDocument.defaultView
          ?.matchMedia?.('(prefers-reduced-motion: reduce)').matches ?? false,
      })
      : decodeGameSave(catalog, saved)
  } catch (error) {
    throw new CursebreakerLaunchError(`Could not restore the game save: ${errorText(error)}`)
  }
  return new CursebreakerRuntime({ ...options, catalog, state })
}
