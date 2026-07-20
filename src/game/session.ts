import type { Diagram } from '../kernel/diagram/diagram'
import { applyStep, type ProofContext } from '../kernel/proof/step'
import { isBlank } from './blank'
import { GameDomainError, type GameStep, type PuzzleDefinition, type PuzzleId } from './types'

export type GameTimeline = {
  readonly states: readonly Diagram[]
  readonly steps: readonly GameStep[]
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
  return { puzzle: puzzle.id, timeline: { states: [puzzle.diagram], steps: [], cursor: 0 } }
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

export function applyGameStep(
  session: GameSession,
  step: GameStep,
  authority: GameRuntimeAuthority,
): GameTransition {
  const current = currentDiagram(session)
  if (isBlank(current)) {
    throw new GameDomainError('cannot apply a game step from canonical blank')
  }
  const next = applyStep(current, step, authority.context, 'backward')
  const states = session.timeline.states.slice(0, session.timeline.cursor + 1)
  const steps = session.timeline.steps.slice(0, session.timeline.cursor)
  const updated: GameSession = {
    ...session,
    timeline: { states: [...states, next], steps: [...steps, step], cursor: steps.length + 1 },
  }
  return { session: updated, completedNow: !isBlank(current) && isBlank(next) }
}
