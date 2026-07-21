import type { Diagram } from '../kernel/diagram/diagram'
import { applyAction, type ProofAction } from '../kernel/proof/action'
import type { ProofContext } from '../kernel/proof/context'
import { actionFromJson, actionToJson } from '../kernel/proof/json'
import { isBlank } from './blank'
import { GameDomainError, type PuzzleDefinition, type PuzzleId } from './types'

export type GameTimeline = {
  readonly states: readonly Diagram[]
  readonly actions: readonly ProofAction[]
  readonly cursor: number
}

export type GameSession = {
  readonly puzzle: PuzzleId
  readonly timeline: GameTimeline
}

export type GameTransition = {
  readonly session: GameSession
  readonly completedNow: boolean
}

export type GameRuntimeAuthority = {
  readonly context: ProofContext
}

export function startPuzzle(puzzle: PuzzleDefinition): GameSession {
  return { puzzle: puzzle.id, timeline: { states: [puzzle.diagram], actions: [], cursor: 0 } }
}

export function currentDiagram(session: GameSession): Diagram {
  const diagram = session.timeline.states[session.timeline.cursor]
  if (diagram === undefined) throw new GameDomainError('game timeline cursor is out of bounds')
  return diagram
}

export function moveCursor(session: GameSession, cursor: number): GameSession {
  if (!Number.isInteger(cursor) || cursor < 0 || cursor >= session.timeline.states.length) {
    throw new GameDomainError(`timeline position ${cursor} is outside 0..${session.timeline.states.length - 1}`)
  }
  return { ...session, timeline: { ...session.timeline, cursor } }
}

export function applyGameAction(
  session: GameSession,
  action: ProofAction,
  authority: GameRuntimeAuthority,
): GameTransition {
  const current = currentDiagram(session)
  if (isBlank(current)) {
    throw new GameDomainError('cannot apply a proof action from canonical blank')
  }
  const ownedAction = actionFromJson(actionToJson(action), 'game proof action')
  const next = applyAction(current, ownedAction, authority.context, 'backward', (diagram, stepIndex) => {
    if (isBlank(diagram) && stepIndex < ownedAction.steps.length - 1) {
      throw new GameDomainError('a proof action cannot continue after reaching canonical blank')
    }
  })

  const states = session.timeline.states.slice(0, session.timeline.cursor + 1)
  const actions = session.timeline.actions.slice(0, session.timeline.cursor)
  const updated: GameSession = {
    ...session,
    timeline: {
      states: [...states, next],
      actions: [...actions, ownedAction],
      cursor: actions.length + 1,
    },
  }
  return { session: updated, completedNow: !isBlank(current) && isBlank(next) }
}
