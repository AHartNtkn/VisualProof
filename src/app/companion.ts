import type { Diagram, WireId } from '../kernel/diagram/diagram'
import type { Replay } from './replay'

/**
 * The app state the companion viewport's content is a pure function of: the
 * current mode, the proof session (if any), which side is being worked, and the
 * active replay (if any). This is exactly the tuple `companionFor` reads — no
 * more — so the queued interface overhaul can hand it a different chrome without
 * touching the decision.
 */
export type CompanionState = {
  readonly mode: 'edit' | 'prove' | 'replay'
  readonly replay: Replay | null
}

/**
 * What the view-only companion viewport renders: the diagram you are working
 * TOWARD, the proper boundary for the side it shows (rendered as frame exits,
 * exactly as the main view does), and a label naming it.
 */
export type Companion = {
  readonly diagram: Diagram
  readonly boundary: readonly WireId[]
  readonly label: string
}

/**
 * Decide what the companion shows, purely and totally over the state tuple.
 * `null` means "hide the companion".
 *
 * - EDIT: null (there is no target to walk toward).
 * - PROVE: null. Fixed-side proving owns two equally interactive live fronts;
 *   a companion must never substitute for either one.
 * - REPLAY: the theorem's final state (the replayed rhs) with the replay
 *   boundary, so the companion is the destination the stepper is heading to.
 *   Independent of the current step k, so at the last step the companion
 *   equals the displayed diagram — still shown; the label says it is the goal.
 * - REPLAY with no active replay: null.
 */
export function companionFor(state: CompanionState): Companion | null {
  if (state.mode === 'replay') {
    const r = state.replay
    if (r === null) return null
    return { diagram: r.diagramAt(r.actionCount), boundary: r.boundary, label: 'goal: final state' }
  }
  return null
}
