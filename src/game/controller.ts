import { artifactTheoremContext, certifyCompletedArtifact } from './artifact-theorem'
import type { ProofAction } from '../kernel/proof/action'
import type { GameCatalog } from './catalog'
import {
  type GameControllerState,
  type InterfaceTextSize,
} from './controller-state'
import { isCultureUnlocked, isUnlocked } from './progress'
import { applyGameAction, currentDiagram, moveCursor, startPuzzle } from './session'
import { guidanceInterventionsFor, type TeacherSignal } from './teaching'
import {
  GameDomainError,
  isGuidanceDelivered,
  type CultureId,
  type PuzzleId,
} from './types'

export type GameAction =
  | { readonly kind: 'selectPuzzle'; readonly puzzle: PuzzleId }
  | { readonly kind: 'applyProofAction'; readonly action: ProofAction }
  | { readonly kind: 'moveTimeline'; readonly cursor: number }
  | { readonly kind: 'escape' }
  | { readonly kind: 'openPause' }
  | { readonly kind: 'resume' }
  | { readonly kind: 'openPauseSettings' }
  | { readonly kind: 'levelSelection' }
  | { readonly kind: 'exitGame' }
  | { readonly kind: 'advanceGuidancePage' }
  | { readonly kind: 'openEditor' }
  | { readonly kind: 'closeEditor' }
  | { readonly kind: 'selectCulture'; readonly culture: CultureId }
  | { readonly kind: 'setCultureScroll'; readonly culture: CultureId; readonly scroll: number }
  | { readonly kind: 'setReducedMotion'; readonly value: boolean }
  | { readonly kind: 'setFullscreen'; readonly value: boolean }
  | { readonly kind: 'setTextSize'; readonly value: InterfaceTextSize }

export type GameEffect =
  | {
      readonly kind: 'selectionRefused'
      readonly puzzle: PuzzleId
      readonly reason: 'locked'
    }
  | {
      readonly kind: 'cultureSelectionRefused'
      readonly culture: CultureId
      readonly reason: 'locked'
    }
  | { readonly kind: 'fullscreenRequested'; readonly fullscreen: boolean }
  | { readonly kind: 'saveBeforeExitAndExitRequested' }

export type GameControllerTransition = {
  readonly state: GameControllerState
  readonly effects: readonly GameEffect[]
}

const result = (
  state: GameControllerState,
  effects: readonly GameEffect[] = [],
): GameControllerTransition => ({ state, effects })

const activePuzzle = (catalog: GameCatalog, state: GameControllerState) => {
  if (state.activePuzzle === null) throw new GameDomainError('controller has no active puzzle')
  return catalog.puzzle(state.activePuzzle)
}

const activeSession = (state: GameControllerState) => {
  if (state.mode !== 'puzzle' || state.activePuzzle === null) {
    throw new GameDomainError('a puzzle timeline is active only in puzzle mode')
  }
  const sessions = state.completedArtifacts.has(state.activePuzzle) ? state.replays : state.firstAttempts
  const session = sessions.get(state.activePuzzle)
  if (session === undefined) {
    throw new GameDomainError(`active puzzle '${state.activePuzzle}' has no stored timeline`)
  }
  return session
}

const requirePause = (state: GameControllerState): void => {
  if (state.transient?.kind !== 'pause') {
    throw new GameDomainError('pause action requires the pause transient')
  }
}

const requireTimelineInputOwner = (state: GameControllerState): void => {
  if (state.transient?.kind === 'pause') {
    throw new GameDomainError('pause transient owns input; proof timeline input is unavailable')
  }
}

const withGuidanceFor = (
  catalog: GameCatalog,
  state: GameControllerState,
  signal: TeacherSignal,
): GameControllerState => {
  if (state.mode !== 'puzzle' || state.activePuzzle === null) {
    return state.guidance === null ? state : { ...state, guidance: null }
  }
  const presented = guidanceInterventionsFor(
    catalog.guidance(state.activePuzzle),
    signal,
    state.deliveredGuidance,
  )[0]
  if (presented === undefined) {
    return state.guidance === null ? state : { ...state, guidance: null }
  }
  const deliveredGuidance = presented.intervention.repeat === 'once'
    && !isGuidanceDelivered(state.deliveredGuidance, presented.identity)
    ? [...state.deliveredGuidance, presented.identity]
    : state.deliveredGuidance
  return {
    ...state,
    deliveredGuidance,
    guidance: { ...presented, page: 0 },
  }
}

export function reduceGame(
  catalog: GameCatalog,
  state: GameControllerState,
  action: GameAction,
): GameControllerTransition {
  switch (action.kind) {
    case 'selectPuzzle': {
      const puzzle = catalog.puzzle(action.puzzle)
      if (!isUnlocked(catalog, { completed: state.completedArtifacts }, puzzle.id)) {
        return result(state, [{ kind: 'selectionRefused', puzzle: puzzle.id, reason: 'locked' }])
      }
      const replay = state.completedArtifacts.has(puzzle.id)
      const sessions = replay ? state.replays : state.firstAttempts
      const session = sessions.get(puzzle.id) ?? startPuzzle(puzzle)
      const selected: GameControllerState = {
        ...state,
        mode: 'puzzle',
        activePuzzle: puzzle.id,
        completionReceipt: null,
        guidance: null,
        transient: null,
        ...(replay
          ? { replays: new Map(state.replays).set(puzzle.id, session) }
          : { firstAttempts: new Map(state.firstAttempts).set(puzzle.id, session) }),
      }
      return result(withGuidanceFor(catalog, selected, { kind: 'opening' }))
    }
    case 'applyProofAction': {
      requireTimelineInputOwner(state)
      const puzzle = activePuzzle(catalog, state)
      const session = activeSession(state)
      const replay = state.completedArtifacts.has(puzzle.id)
      const transition = applyGameAction(session, action.action, {
        context: artifactTheoremContext(catalog, state.completedArtifacts),
      })
      if (transition.completedNow) {
        if (replay) {
          const replays = new Map(state.replays)
          replays.delete(puzzle.id)
          return result({
            ...state,
            mode: 'completion',
            replays,
            completionReceipt: {
              puzzle: puzzle.id,
              moves: transition.session.timeline.cursor,
              replay: true,
            },
            guidance: null,
            transient: null,
          })
        }
        const completedArtifact = certifyCompletedArtifact(
          catalog,
          state.completedArtifacts,
          puzzle,
          transition.session.timeline.actions.slice(0, transition.session.timeline.cursor),
        )
        const firstAttempts = new Map(state.firstAttempts)
        firstAttempts.delete(puzzle.id)
        return result({
          ...state,
          mode: 'completion',
          completedArtifacts: new Map(state.completedArtifacts).set(puzzle.id, completedArtifact),
          firstAttempts,
          completionReceipt: {
            puzzle: puzzle.id,
            moves: transition.session.timeline.cursor,
            replay: false,
          },
          guidance: null,
          transient: null,
        })
      }
      if (replay) {
        return result(withGuidanceFor(catalog, {
          ...state,
          replays: new Map(state.replays).set(puzzle.id, transition.session),
          guidance: null,
        }, { kind: 'recognizedUnwinnable', diagram: currentDiagram(transition.session) }))
      }
      return result(withGuidanceFor(catalog, {
        ...state,
        firstAttempts: new Map(state.firstAttempts).set(puzzle.id, transition.session),
        guidance: null,
      }, { kind: 'recognizedUnwinnable', diagram: currentDiagram(transition.session) }))
    }
    case 'moveTimeline': {
      requireTimelineInputOwner(state)
      const puzzle = activePuzzle(catalog, state)
      const session = moveCursor(activeSession(state), action.cursor)
      if (state.completedArtifacts.has(puzzle.id)) {
        return result(withGuidanceFor(catalog, {
          ...state,
          replays: new Map(state.replays).set(puzzle.id, session),
          guidance: null,
        }, { kind: 'recognizedUnwinnable', diagram: currentDiagram(session) }))
      }
      return result(withGuidanceFor(catalog, {
        ...state,
        firstAttempts: new Map(state.firstAttempts).set(puzzle.id, session),
        guidance: null,
      }, { kind: 'recognizedUnwinnable', diagram: currentDiagram(session) }))
    }
    case 'escape': {
      if (state.transient === null) {
        return result({ ...state, transient: { kind: 'pause', presentation: 'menu' } })
      }
      if (state.transient.kind === 'pause' && state.transient.presentation === 'settings') {
        return result({ ...state, transient: { kind: 'pause', presentation: 'menu' } })
      }
      return result({ ...state, transient: null })
    }
    case 'openPause':
      return result({ ...state, transient: { kind: 'pause', presentation: 'menu' } })
    case 'resume':
      requirePause(state)
      return result({ ...state, transient: null })
    case 'openPauseSettings':
      requirePause(state)
      return result({ ...state, transient: { kind: 'pause', presentation: 'settings' } })
    case 'levelSelection':
      return result({
        ...state,
        mode: 'archive',
        activePuzzle: null,
        completionReceipt: null,
        guidance: null,
        transient: null,
      })
    case 'exitGame':
      requirePause(state)
      return result(state, [{ kind: 'saveBeforeExitAndExitRequested' }])
    case 'advanceGuidancePage': {
      const guidance = state.guidance
      if (guidance === null || guidance.page >= guidance.intervention.pages.length - 1) {
        return result(state)
      }
      return result({ ...state, guidance: { ...guidance, page: guidance.page + 1 } })
    }
    case 'openEditor':
      activePuzzle(catalog, state)
      return result({ ...state, transient: { kind: 'editor' } })
    case 'closeEditor':
      if (state.transient?.kind !== 'editor') return result(state)
      return result({ ...state, transient: null })
    case 'selectCulture': {
      catalog.culture(action.culture)
      if (!isCultureUnlocked(catalog, { completed: state.completedArtifacts }, action.culture)) {
        return result(state, [{
          kind: 'cultureSelectionRefused', culture: action.culture, reason: 'locked',
        }])
      }
      return result({ ...state, selectedCulture: action.culture })
    }
    case 'setCultureScroll': {
      catalog.culture(action.culture)
      if (!Number.isFinite(action.scroll) || action.scroll < 0) {
        throw new GameDomainError('culture scroll must be nonnegative finite')
      }
      return result({
        ...state,
        scrollByCulture: new Map(state.scrollByCulture).set(action.culture, action.scroll),
      })
    }
    case 'setReducedMotion':
      if (state.settings.reducedMotion === action.value) return result(state)
      return result({ ...state, settings: { ...state.settings, reducedMotion: action.value } })
    case 'setFullscreen':
      if (state.settings.fullscreen === action.value) return result(state)
      return result(
        { ...state, settings: { ...state.settings, fullscreen: action.value } },
        [{ kind: 'fullscreenRequested', fullscreen: action.value }],
      )
    case 'setTextSize':
      if (state.settings.textSize === action.value) return result(state)
      return result({ ...state, settings: { ...state.settings, textSize: action.value } })
  }
}
