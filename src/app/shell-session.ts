import type { Diagram, WireId } from '../kernel/diagram/diagram'
import type { Replay } from './replay'
import type { ProofSession, TrackSession } from './session'
import { currentSide, currentTrack, sideBoundary, trackBoundary } from './session'

export type ActiveProof =
  | { readonly kind: 'track'; readonly track: TrackSession }
  | { readonly kind: 'dual'; readonly session: ProofSession; readonly side: 'forward' | 'backward' }

export type EditShellSession = { readonly kind: 'edit' }
export type ProveShellSession = { readonly kind: 'prove'; readonly proof: ActiveProof }
export type NonReplayShellSession = EditShellSession | ProveShellSession

export type ReplayShellSession = {
  readonly kind: 'replay'
  readonly replay: Replay
  readonly cursor: number
  readonly returnTo: NonReplayShellSession
}

export type ShellSession = NonReplayShellSession | ReplayShellSession

export function editShellSession(): EditShellSession {
  return { kind: 'edit' }
}

export function proofShellSession(proof: ActiveProof): ProveShellSession {
  return { kind: 'prove', proof }
}

export function enterShellReplay(state: ShellSession, replay: Replay): ReplayShellSession {
  return {
    kind: 'replay',
    replay,
    cursor: 0,
    returnTo: state.kind === 'replay' ? state.returnTo : state,
  }
}

export function moveShellReplay(state: ReplayShellSession, cursor: number): ReplayShellSession {
  return {
    ...state,
    cursor: Math.max(0, Math.min(state.replay.actionCount, cursor)),
  }
}

export function leaveShellReplay(state: ReplayShellSession): NonReplayShellSession {
  return state.returnTo
}

export function proofForShellSession(state: ShellSession): ActiveProof | null {
  const active = state.kind === 'replay' ? state.returnTo : state
  return active.kind === 'prove' ? active.proof : null
}

export function diagramForShellSession(state: ShellSession, editDiagram: Diagram): Diagram {
  if (state.kind === 'replay') return state.replay.diagramAt(state.cursor)
  if (state.kind === 'edit') return editDiagram
  return state.proof.kind === 'track'
    ? currentTrack(state.proof.track)
    : currentSide(state.proof.session, state.proof.side)
}

export function shellSessionBoundary(state: ShellSession): readonly WireId[] {
  if (state.kind === 'replay') return state.replay.boundaryAt(state.cursor)
  if (state.kind === 'edit') return []
  return state.proof.kind === 'track'
    ? trackBoundary(state.proof.track)
    : sideBoundary(state.proof.session, state.proof.side)
}
