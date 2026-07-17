import { artifactTheoremContext } from './artifact-theorem'
import type { GameCatalog } from './catalog'
import {
  type GameControllerState,
  type InterfaceTextSize,
} from './controller-state'
import { isCultureUnlocked, isUnlocked } from './progress'
import { applyGameStep, moveCursor, startPuzzle } from './session'
import type { TeacherPresentationIntent } from './teaching'
import {
  GameDomainError,
  type CultureId,
  type GameStep,
  type PuzzleId,
  type TeacherIntervention,
} from './types'

export type GameAction =
  | { readonly kind: 'selectPuzzle'; readonly puzzle: PuzzleId }
  | { readonly kind: 'applyStep'; readonly step: GameStep }
  | { readonly kind: 'moveTimeline'; readonly cursor: number }
  | { readonly kind: 'escape' }
  | { readonly kind: 'openPause' }
  | { readonly kind: 'resume' }
  | { readonly kind: 'openPauseSettings' }
  | { readonly kind: 'levelSelection' }
  | { readonly kind: 'exitGame' }
  | { readonly kind: 'openTeacher'; readonly intervention: TeacherIntervention }
  | { readonly kind: 'acknowledgeTeacher' }
  | { readonly kind: 'closeTeacher' }
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
  const sessions = state.completed.has(state.activePuzzle) ? state.replays : state.firstAttempts
  const session = sessions.get(state.activePuzzle)
  if (session === undefined) {
    throw new GameDomainError(`active puzzle '${state.activePuzzle}' has no stored timeline`)
  }
  return session
}

const teacherPresentation = (intervention: TeacherIntervention): TeacherPresentationIntent => {
  switch (intervention.trigger.kind) {
    case 'opening': return { kind: 'modalInstruction' }
    case 'completion': return { kind: 'completionCommentary' }
    case 'recognizedUnwinnable': return { kind: 'nonblockingCommentary', recovery: 'timeline' }
  }
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
  if (
    state.transient?.kind === 'teacher'
    && state.transient.presentation.kind !== 'nonblockingCommentary'
  ) {
    throw new GameDomainError('modal teacher transient owns input; proof timeline input is unavailable')
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
      if (!isUnlocked(catalog, { completed: state.completed }, puzzle.id)) {
        return result(state, [{ kind: 'selectionRefused', puzzle: puzzle.id, reason: 'locked' }])
      }
      const replay = state.completed.has(puzzle.id)
      const sessions = replay ? state.replays : state.firstAttempts
      const session = sessions.get(puzzle.id) ?? startPuzzle(puzzle)
      return result({
        ...state,
        mode: 'puzzle',
        activePuzzle: puzzle.id,
        completionReceipt: null,
        transient: null,
        ...(replay
          ? { replays: new Map(state.replays).set(puzzle.id, session) }
          : { firstAttempts: new Map(state.firstAttempts).set(puzzle.id, session) }),
      })
    }
    case 'applyStep': {
      requireTimelineInputOwner(state)
      const puzzle = activePuzzle(catalog, state)
      const session = activeSession(state)
      const replay = state.completed.has(puzzle.id)
      const transition = applyGameStep(session, action.step, {
        context: artifactTheoremContext(
          catalog.source.puzzles,
          state.completed,
          catalog.source.context,
        ),
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
              moves: transition.session.timeline.states.length - 1,
              replay: true,
            },
            transient: null,
          })
        }
        const firstAttempts = new Map(state.firstAttempts)
        firstAttempts.delete(puzzle.id)
        return result({
          ...state,
          mode: 'completion',
          completed: new Set(state.completed).add(puzzle.id),
          firstAttempts,
          completionReceipt: {
            puzzle: puzzle.id,
            moves: transition.session.timeline.states.length - 1,
            replay: false,
          },
          transient: null,
        })
      }
      if (replay) {
        return result({
          ...state,
          replays: new Map(state.replays).set(puzzle.id, transition.session),
        })
      }
      return result({
        ...state,
        firstAttempts: new Map(state.firstAttempts).set(puzzle.id, transition.session),
      })
    }
    case 'moveTimeline': {
      requireTimelineInputOwner(state)
      const puzzle = activePuzzle(catalog, state)
      const session = moveCursor(activeSession(state), action.cursor)
      if (state.completed.has(puzzle.id)) {
        return result({ ...state, replays: new Map(state.replays).set(puzzle.id, session) })
      }
      return result({ ...state, firstAttempts: new Map(state.firstAttempts).set(puzzle.id, session) })
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
        transient: null,
      })
    case 'exitGame':
      requirePause(state)
      return result(state, [{ kind: 'saveBeforeExitAndExitRequested' }])
    case 'openTeacher': {
      const puzzle = activePuzzle(catalog, state)
      const intervention = puzzle.teacher.find((candidate) => candidate.id === action.intervention.id)
      if (intervention === undefined) {
        throw new GameDomainError(
          `puzzle '${puzzle.id}' has no authored teacher intervention '${action.intervention.id}'`,
        )
      }
      if (intervention.repeat === 'once' && state.acknowledgedTeachers.has(intervention.id)) {
        return result(state)
      }
      return result({
        ...state,
        transient: {
          kind: 'teacher',
          intervention,
          presentation: teacherPresentation(intervention),
        },
      })
    }
    case 'acknowledgeTeacher': {
      if (state.transient?.kind !== 'teacher') {
        throw new GameDomainError('teacher acknowledgement requires a presented intervention')
      }
      const acknowledgedTeachers = state.transient.intervention.repeat === 'once'
        ? new Set(state.acknowledgedTeachers).add(state.transient.intervention.id)
        : state.acknowledgedTeachers
      return result({ ...state, acknowledgedTeachers, transient: null })
    }
    case 'closeTeacher':
      if (state.transient?.kind !== 'teacher') return result(state)
      return result({ ...state, transient: null })
    case 'openEditor':
      activePuzzle(catalog, state)
      return result({ ...state, transient: { kind: 'editor' } })
    case 'closeEditor':
      if (state.transient?.kind !== 'editor') return result(state)
      return result({ ...state, transient: null })
    case 'selectCulture': {
      catalog.culture(action.culture)
      if (!isCultureUnlocked(catalog, { completed: state.completed }, action.culture)) {
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
