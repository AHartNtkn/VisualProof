import type { Diagram, WireId } from '../kernel/diagram/diagram'
import type { DiagramWithBoundary } from '../kernel/diagram/boundary'
import { exploreForm } from '../kernel/diagram/canonical/explore'
import { transportBoundary } from '../kernel/proof/step'
import type { StepReceipt } from '../kernel/proof/step'
import type { ProofContext } from '../kernel/proof/context'
import { assertProofContext, registerTheorem } from '../kernel/proof/context'
import type { ProofAction } from '../kernel/proof/action'
import { applyAction } from '../kernel/proof/action'
import type { Theorem } from '../kernel/proof/theorem'
import { checkTheorem } from '../kernel/proof/theorem'

export type ProofTimeline = {
  readonly states: readonly Diagram[]
  readonly boundaries: readonly (readonly WireId[])[]
  readonly actions: readonly ProofAction[]
  readonly cursor: number
}

export type ProofSession = {
  readonly lhs: DiagramWithBoundary
  readonly rhs: DiagramWithBoundary
  readonly ctx: ProofContext
  readonly forward: ProofTimeline
  /** The backward side records the user's flip-gated steps AS GIVEN; they
      replay from the rhs at declaration (checkTheorem's dual replay). */
  readonly backward: ProofTimeline
}

export type TrackDirection = 'forward' | 'backward'

/** One-origin proving: the current sheet is the fixed end and the other end is
    derived by the user's track. This is the ordinary proof workflow; a
    two-ended ProofSession is reserved for an explicitly fixed statement. */
export type TrackSession = {
  readonly origin: DiagramWithBoundary
  readonly direction: TrackDirection
  readonly ctx: ProofContext
  readonly timeline: ProofTimeline
}

function startTimeline(origin: Diagram, boundary: readonly WireId[]): ProofTimeline {
  return { states: [origin], boundaries: [boundary], actions: [], cursor: 0 }
}

export function timelineCurrent(timeline: ProofTimeline): Diagram {
  const current = timeline.states[timeline.cursor]
  if (current === undefined) throw new Error('proof timeline cursor is out of bounds')
  return current
}

export function timelineBoundary(timeline: ProofTimeline): readonly WireId[] {
  const boundary = timeline.boundaries[timeline.cursor]
  if (boundary === undefined) throw new Error('proof timeline boundary cursor is out of bounds')
  return boundary
}

/** The proof currently selected by the cursor. Retained actions beyond
    the cursor belong to redo history and are not part of the active proof. */
export function timelineActiveActions(timeline: ProofTimeline): readonly ProofAction[] {
  return timeline.actions.slice(0, timeline.cursor)
}

export function moveTimeline(timeline: ProofTimeline, cursor: number): ProofTimeline {
  if (!Number.isInteger(cursor) || cursor < 0 || cursor >= timeline.states.length) {
    throw new Error(`history position ${cursor} is outside 0..${timeline.states.length - 1}`)
  }
  return cursor === timeline.cursor ? timeline : { ...timeline, cursor }
}

function appendTimeline(
  timeline: ProofTimeline,
  action: ProofAction,
  next: Diagram,
  boundary: readonly WireId[],
): ProofTimeline {
  const states = timeline.states.slice(0, timeline.cursor + 1)
  const boundaries = timeline.boundaries.slice(0, timeline.cursor + 1)
  const actions = timeline.actions.slice(0, timeline.cursor)
  return {
    states: [...states, next],
    boundaries: [...boundaries, boundary],
    actions: [...actions, action],
    cursor: actions.length + 1,
  }
}

export function startTrack(origin: DiagramWithBoundary, direction: TrackDirection, ctx: ProofContext): TrackSession {
  assertProofContext(ctx)
  return { origin, direction, ctx, timeline: startTimeline(origin.diagram, origin.boundary) }
}

function assertTrack(track: TrackSession): void {
  assertProofContext(track.ctx)
}

function assertSession(session: ProofSession): void {
  assertProofContext(session.ctx)
}

export function currentTrack(track: TrackSession): Diagram {
  assertTrack(track)
  return timelineCurrent(track.timeline)
}

export function trackBoundary(track: TrackSession): readonly WireId[] {
  assertTrack(track)
  return timelineBoundary(track.timeline)
}

function applyActionWithBoundary(
  diagram: Diagram,
  boundary: readonly WireId[],
  action: ProofAction,
  ctx: ProofContext,
  orientation: TrackDirection,
  owner: string,
): { readonly diagram: Diagram; readonly boundary: readonly WireId[] } {
  let mappedBoundary = boundary
  const result = applyAction(diagram, action, ctx, orientation, (_next, stepIndex, receipt: StepReceipt) => {
    const mapped = transportBoundary(receipt.interface, mappedBoundary)
    if (mapped === undefined) {
      const missing = mappedBoundary.find((wire) => receipt.interface.image(wire) === undefined)
      throw new Error(
        `${owner} step ${stepIndex} gives boundary wire '${missing ?? '<unknown>'}' no semantic image`,
      )
    }
    mappedBoundary = mapped
  })
  return { diagram: result, boundary: mappedBoundary }
}

export function applyTrack(track: TrackSession, action: ProofAction): TrackSession {
  assertTrack(track)
  const current = currentTrack(track)
  const next = applyActionWithBoundary(
    current,
    trackBoundary(track),
    action,
    track.ctx,
    track.direction,
    `${track.direction} track`,
  )
  return {
    ...track,
    timeline: appendTimeline(track.timeline, action, next.diagram, next.boundary),
  }
}

export function moveTrack(track: TrackSession, cursor: number): TrackSession {
  assertTrack(track)
  return { ...track, timeline: moveTimeline(track.timeline, cursor) }
}

export function undoTrack(track: TrackSession): TrackSession {
  assertTrack(track)
  if (track.timeline.cursor === 0) throw new Error(`nothing to undo on the ${track.direction} track`)
  return moveTrack(track, track.timeline.cursor - 1)
}

export function redoTrack(track: TrackSession): TrackSession {
  assertTrack(track)
  if (track.timeline.cursor === track.timeline.states.length - 1) throw new Error(`nothing to redo on the ${track.direction} track`)
  return moveTrack(track, track.timeline.cursor + 1)
}

export function declareTrack(track: TrackSession, name: string): Theorem {
  assertTrack(track)
  const current = { diagram: currentTrack(track), boundary: trackBoundary(track) }
  const actions = timelineActiveActions(track.timeline)
  const theorem: Theorem = track.direction === 'forward'
    ? { name, lhs: track.origin, rhs: current, actions }
    : { name, lhs: current, rhs: track.origin, actions: [], backActions: actions }
  checkTheorem(theorem, track.ctx)
  return theorem
}

export function adoptTrackTheorem(track: TrackSession, theorem: Theorem): TrackSession {
  assertTrack(track)
  if (track.ctx.theorems.has(theorem.name)) throw new Error(`'${theorem.name}' already names a theorem in this session`)
  return { ...track, ctx: registerTheorem(track.ctx, theorem) }
}

/**
 * The current ordered boundary of a proof side, transported by every executed
 * step and restored together with the diagram by history navigation.
 */
export function sideBoundary(s: ProofSession, side: 'forward' | 'backward'): readonly WireId[] {
  assertSession(s)
  return timelineBoundary(s[side])
}

export function startSession(lhs: DiagramWithBoundary, rhs: DiagramWithBoundary, ctx: ProofContext): ProofSession {
  assertProofContext(ctx)
  return {
    lhs, rhs, ctx,
    forward: startTimeline(lhs.diagram, lhs.boundary),
    backward: startTimeline(rhs.diagram, rhs.boundary),
  }
}

export function currentSide(s: ProofSession, side: 'forward' | 'backward'): Diagram {
  assertSession(s)
  return timelineCurrent(s[side])
}

export function moveSide(s: ProofSession, side: 'forward' | 'backward', cursor: number): ProofSession {
  assertSession(s)
  return { ...s, [side]: moveTimeline(s[side], cursor) }
}

/** Apply a forward step through the kernel; refusals propagate untouched. */
export function applyForward(s: ProofSession, action: ProofAction): ProofSession {
  assertSession(s)
  const next = applyActionWithBoundary(
    currentSide(s, 'forward'),
    sideBoundary(s, 'forward'),
    action,
    s.ctx,
    'forward',
    'forward',
  )
  return {
    ...s,
    forward: appendTimeline(s.forward, action, next.diagram, next.boundary),
  }
}

export function undoForward(s: ProofSession): ProofSession {
  assertSession(s)
  if (s.forward.cursor === 0) throw new Error('nothing to undo on the forward side')
  return moveSide(s, 'forward', s.forward.cursor - 1)
}

export function redoForward(s: ProofSession): ProofSession {
  assertSession(s)
  if (s.forward.cursor === s.forward.states.length - 1) throw new Error('nothing to redo on the forward side')
  return moveSide(s, 'forward', s.forward.cursor + 1)
}

/**
 * Backward actions transform the GOAL side: the user removes structure the
 * forward direction would add. Each action computes the inverse-applied
 * diagram G′ and the forward step (G′ → G) TOGETHER, then asserts that
 * replaying the step on G′ reproduces G semantically (by fingerprint) — keeping
 * the recorded tail replayable without id-rewriting anywhere except the meet.
 */
/**
 * Backward proving takes ORDINARY steps and RECORDS them as given (USER
 * redesign ruling: no inverse construction of any kind). Execution is the
 * same appliers with orientation='backward' — the calculus's cut symmetry
 * flips exactly the polarity gates. Verification is checkTheorem's dual
 * replay: the recorded backward steps replay from the RHS at declaration,
 * so a mistake here cannot certify anything.
 */
export function applyBackward(s: ProofSession, action: ProofAction): ProofSession {
  assertSession(s)
  const g = currentSide(s, 'backward')
  const gPrime = applyActionWithBoundary(
    g,
    sideBoundary(s, 'backward'),
    action,
    s.ctx,
    'backward',
    'backward',
  )
  return {
    ...s,
    backward: appendTimeline(s.backward, action, gPrime.diagram, gPrime.boundary),
  }
}

export function undoBackward(s: ProofSession): ProofSession {
  assertSession(s)
  if (s.backward.cursor === 0) throw new Error('nothing to undo on the backward side')
  return moveSide(s, 'backward', s.backward.cursor - 1)
}

export function redoBackward(s: ProofSession): ProofSession {
  assertSession(s)
  if (s.backward.cursor === s.backward.states.length - 1) throw new Error('nothing to redo on the backward side')
  return moveSide(s, 'backward', s.backward.cursor + 1)
}

export function meet(s: ProofSession): boolean {
  assertSession(s)
  return exploreForm(currentSide(s, 'forward'), sideBoundary(s, 'forward'))
    === exploreForm(currentSide(s, 'backward'), sideBoundary(s, 'backward'))
}

/** Both halves AS RECORDED become the theorem (caller runs checkTheorem —
    its dual replay verifies each half from its own end and the meet). */
export function assembleTheorem(s: ProofSession, name: string): Theorem {
  assertSession(s)
  if (!meet(s)) throw new Error('the two sides have not met; nothing to assemble')
  return {
    name,
    lhs: s.lhs,
    rhs: s.rhs,
    actions: timelineActiveActions(s.forward),
    backActions: timelineActiveActions(s.backward),
  }
}

/** Verify and add a finished theorem to the session context — citable from now on. */
export function adoptTheorem(s: ProofSession, thm: Theorem): ProofSession {
  assertSession(s)
  if (s.ctx.theorems.has(thm.name)) throw new Error(`'${thm.name}' already names a theorem in this session`)
  return { ...s, ctx: registerTheorem(s.ctx, thm) }
}
