import { ProofFrontViewport, defaultMotionPreferences, type ProofFrontDebugState } from '../../app'
import type { KeySample } from '../../app/interact/viewport'
import type { Vec2 } from '../../view/vec'
import { DARK } from '../../view/paint'
import { openingCatalog } from '../content'
import { emptyProgress, isUnlocked, recordCompletion, type GameProgress } from '../progress'
import {
  applyGameStep,
  currentDiagram,
  moveCursor,
  startPuzzle,
  type GameRuntimeAuthority,
  type GameSession,
} from '../session'
import { puzzleId, type GameStep, type PuzzleId } from '../types'
import { lensLayout } from './lens-layout'
import { mountTimelineLever } from './timeline-lever'

const DEFAULT_PUZZLE = puzzleId('two-veils')
const REFUSAL_LIFETIME_MS = 1800

export type CursebreakerMountOptions = {
  readonly host: HTMLElement
  readonly initialPuzzle?: PuzzleId
}

export type CursebreakerRect = {
  readonly left: number
  readonly top: number
  readonly width: number
  readonly height: number
}

export type CursebreakerDebugState = {
  readonly puzzle: PuzzleId
  readonly timeline: { readonly cursor: number; readonly count: number }
  readonly completed: readonly PuzzleId[]
  readonly lens: CursebreakerRect
  readonly glass: CursebreakerRect
  readonly viewport: ProofFrontDebugState
}

export type MountedCursebreaker = {
  dispose(): void
  debug(): CursebreakerDebugState
  canvasToClient(worldPoint: Vec2): Vec2
}

const rectSnapshot = (element: Element): CursebreakerRect => {
  const rect = element.getBoundingClientRect()
  return { left: rect.left, top: rect.top, width: rect.width, height: rect.height }
}

const decorativeImage = (className: string, source: URL): HTMLImageElement => {
  const image = document.createElement('img')
  image.className = `${className} curse-decoration`
  image.src = source.href
  image.alt = ''
  image.setAttribute('aria-hidden', 'true')
  return image
}

export function mountCursebreaker(options: CursebreakerMountOptions): MountedCursebreaker {
  const catalog = openingCatalog()
  const selected = options.initialPuzzle ?? DEFAULT_PUZZLE
  let progress: GameProgress = emptyProgress()
  if (!isUnlocked(catalog, progress, selected)) {
    throw new Error(`puzzle '${selected}' is locked by incomplete prerequisites`)
  }

  let session: GameSession = startPuzzle(catalog.puzzle(selected))
  const authority: GameRuntimeAuthority = {
    context: catalog.source.context,
    puzzle: (id) => catalog.puzzle(id),
    canUseVellum: (id) => progress.completed.has(id) && catalog.puzzle(id).grantsVellum,
  }
  const motionPreferences = defaultMotionPreferences(
    window.matchMedia?.('(prefers-reduced-motion: reduce)').matches ?? false,
  )

  options.host.replaceChildren()
  const stage = document.createElement('div')
  stage.className = 'curse-lens-stage'
  const shadow = decorativeImage(
    'curse-lens-shadow',
    new URL('../../../assets/interface/generated/central-lens/shadow.png', import.meta.url),
  )
  const glass = document.createElement('div')
  glass.className = 'curse-lens-glass'
  const canvas = document.createElement('canvas')
  canvas.id = 'seal-canvas'
  canvas.setAttribute('aria-label', 'Seal under examination')
  glass.append(canvas)
  const optics = decorativeImage(
    'curse-lens-optics',
    new URL('../../../assets/interface/generated/central-lens/glass.png', import.meta.url),
  )
  const frame = document.createElement('div')
  frame.className = 'curse-lens-frame curse-decoration'
  frame.setAttribute('aria-hidden', 'true')
  stage.append(shadow, glass, optics, frame)
  options.host.append(stage)

  let focused = true
  let refusal: HTMLOutputElement | null = null
  let refusalTimer: number | null = null
  let lever: ReturnType<typeof mountTimelineLever>

  const clearRefusal = (): void => {
    refusal?.remove()
    refusal = null
    if (refusalTimer !== null) window.clearTimeout(refusalTimer)
    refusalTimer = null
  }
  const presentRefusal = (text: string, pointer: Vec2): void => {
    clearRefusal()
    const output = document.createElement('output')
    output.className = 'curse-refusal'
    output.setAttribute('role', 'alert')
    output.textContent = text
    output.style.left = `${pointer.x + 12}px`
    output.style.top = `${pointer.y + 12}px`
    document.body.append(output)
    refusal = output
    refusalTimer = window.setTimeout(clearRefusal, REFUSAL_LIFETIME_MS)
  }

  const reconcile = (): void => {
    viewport.reconcileDiagram()
    lever.refresh()
  }
  const requestCursor = (cursor: number, pointer?: Vec2): void => {
    try {
      session = moveCursor(session, cursor)
      reconcile()
    } catch (error) {
      if (pointer !== undefined) {
        presentRefusal(error instanceof Error ? error.message : String(error), pointer)
      }
    }
  }
  const keyCommand = (sample: KeySample): boolean => {
    if (sample.altKey || (!sample.ctrlKey && !sample.metaKey) || sample.key.toLowerCase() !== 'z') {
      return false
    }
    const rect = canvas.getBoundingClientRect()
    requestCursor(session.timeline.cursor + (sample.shiftKey ? 1 : -1), {
      x: rect.left + rect.width / 2,
      y: rect.top + rect.height / 2,
    })
    return true
  }

  const viewport = new ProofFrontViewport(canvas, {
    side: 'backward',
    diagram: () => currentDiagram(session),
    boundary: () => [],
    context: () => ({ relations: catalog.source.context.relations, theorems: new Map() }),
    theme: () => DARK,
    fuel: () => 256,
    prepare: (step) => {
      const transition = applyGameStep(session, step as GameStep, authority)
      return () => {
        session = transition.session
        if (transition.completedNow && !progress.completed.has(session.puzzle)) {
          progress = recordCompletion(progress, session.puzzle)
        }
        reconcile()
      }
    },
    motionPreferences: () => motionPreferences,
    workspaceInputAllowed: () => true,
    focused: () => focused,
    focus: () => { focused = true },
    keyCommand,
    refuse: presentRefusal,
    changed: () => {},
  })

  lever = mountTimelineLever(stage, () => session.timeline, requestCursor, () => !viewport.playing)

  const applyLayout = (): void => {
    const layout = lensLayout(window.innerWidth, window.innerHeight)
    stage.style.left = `${layout.left}px`
    stage.style.top = `${layout.top}px`
    stage.style.width = `${layout.size}px`
    stage.style.height = `${layout.size}px`
  }
  applyLayout()
  window.addEventListener('resize', applyLayout)

  const observer = new ResizeObserver((entries) => {
    const entry = entries.find((candidate) => candidate.target === glass)
    if (entry !== undefined) viewport.resize(entry.contentRect.width, entry.contentRect.height)
  })
  observer.observe(glass)

  let frameRequest = 0
  const animate = (now: number): void => {
    viewport.frame(now)
    frameRequest = window.requestAnimationFrame(animate)
  }
  frameRequest = window.requestAnimationFrame(animate)

  let disposed = false
  return {
    dispose: () => {
      if (disposed) return
      disposed = true
      window.cancelAnimationFrame(frameRequest)
      window.removeEventListener('resize', applyLayout)
      observer.disconnect()
      clearRefusal()
      lever.dispose()
      viewport.dispose()
      stage.remove()
      focused = false
    },
    debug: () => ({
      puzzle: session.puzzle,
      timeline: { cursor: session.timeline.cursor, count: session.timeline.states.length },
      completed: [...progress.completed],
      lens: rectSnapshot(stage),
      glass: rectSnapshot(glass),
      viewport: viewport.debugState(),
    }),
    canvasToClient: (worldPoint) => {
      const rect = canvas.getBoundingClientRect()
      return {
        x: rect.left + (worldPoint.x * viewport.view.scale + viewport.view.offsetX) * rect.width / canvas.width,
        y: rect.top + (worldPoint.y * viewport.view.scale + viewport.view.offsetY) * rect.height / canvas.height,
      }
    },
  }
}
