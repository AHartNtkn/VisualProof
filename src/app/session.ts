import type { Diagram, WireId } from '../kernel/diagram/diagram'
import type { DiagramWithBoundary } from '../kernel/diagram/boundary'
import { exploreForm } from '../kernel/diagram/canonical/explore'
import type { ProofContext, ProofStep } from '../kernel/proof/step'
import { applyStep } from '../kernel/proof/step'
import type { Theorem } from '../kernel/proof/theorem'
import { checkTheorem } from '../kernel/proof/theorem'

export type ProofTimeline = {
  readonly states: readonly Diagram[]
  readonly steps: readonly ProofStep[]
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

function startTimeline(origin: Diagram): ProofTimeline {
  return { states: [origin], steps: [], cursor: 0 }
}

export function timelineCurrent(timeline: ProofTimeline): Diagram {
  const current = timeline.states[timeline.cursor]
  if (current === undefined) throw new Error('proof timeline cursor is out of bounds')
  return current
}

export function moveTimeline(timeline: ProofTimeline, cursor: number): ProofTimeline {
  if (!Number.isInteger(cursor) || cursor < 0 || cursor >= timeline.states.length) {
    throw new Error(`history position ${cursor} is outside 0..${timeline.states.length - 1}`)
  }
  return cursor === timeline.cursor ? timeline : { ...timeline, cursor }
}

function appendTimeline(timeline: ProofTimeline, step: ProofStep, next: Diagram): ProofTimeline {
  const states = timeline.states.slice(0, timeline.cursor + 1)
  const steps = timeline.steps.slice(0, timeline.cursor)
  return { states: [...states, next], steps: [...steps, step], cursor: steps.length + 1 }
}

export function startTrack(origin: DiagramWithBoundary, direction: TrackDirection, ctx: ProofContext): TrackSession {
  return { origin, direction, ctx, timeline: startTimeline(origin.diagram) }
}

export function currentTrack(track: TrackSession): Diagram {
  return timelineCurrent(track.timeline)
}

export function trackBoundary(track: TrackSession): readonly WireId[] {
  const current = currentTrack(track)
  return track.origin.boundary.filter((wire) => current.wires[wire] !== undefined)
}

export function applyTrack(track: TrackSession, step: ProofStep): TrackSession {
  const current = currentTrack(track)
  const next = track.direction === 'forward'
    ? applyStep(current, step, track.ctx)
    : applyStep(current, step, track.ctx, 'backward')
  return { ...track, timeline: appendTimeline(track.timeline, step, next) }
}

export function moveTrack(track: TrackSession, cursor: number): TrackSession {
  return { ...track, timeline: moveTimeline(track.timeline, cursor) }
}

export function undoTrack(track: TrackSession): TrackSession {
  if (track.timeline.cursor === 0) throw new Error(`nothing to undo on the ${track.direction} track`)
  return moveTrack(track, track.timeline.cursor - 1)
}

export function redoTrack(track: TrackSession): TrackSession {
  if (track.timeline.cursor === track.timeline.states.length - 1) throw new Error(`nothing to redo on the ${track.direction} track`)
  return moveTrack(track, track.timeline.cursor + 1)
}

export function declareTrack(track: TrackSession, name: string): Theorem {
  const current = { diagram: currentTrack(track), boundary: trackBoundary(track) }
  const steps = track.timeline.steps.slice(0, track.timeline.cursor)
  const theorem: Theorem = track.direction === 'forward'
    ? { name, lhs: track.origin, rhs: current, steps }
    : { name, lhs: current, rhs: track.origin, steps: [], backSteps: steps }
  checkTheorem(theorem, track.ctx)
  return theorem
}

export function adoptTrackTheorem(track: TrackSession, theorem: Theorem): TrackSession {
  if (track.ctx.theorems.has(theorem.name)) throw new Error(`'${theorem.name}' already names a theorem in this session`)
  checkTheorem(theorem, track.ctx)
  const theorems = new Map(track.ctx.theorems)
  theorems.set(theorem.name, theorem)
  return { ...track, ctx: { theorems, relations: track.ctx.relations } }
}

/**
 * The boundary wires of a side's statement: the forward side proves from the
 * lhs, the backward side from the rhs, so each renders its own boundary as
 * frame exits. Ids are stable across a side's proof steps (the proof transforms
 * the interior; the interface persists), so this is the boundary the render
 * engine receives for that side.
 */
export function sideBoundary(s: ProofSession, side: 'forward' | 'backward'): readonly WireId[] {
  return side === 'forward' ? s.lhs.boundary : s.rhs.boundary
}

export function startSession(lhs: DiagramWithBoundary, rhs: DiagramWithBoundary, ctx: ProofContext): ProofSession {
  return {
    lhs, rhs, ctx,
    forward: startTimeline(lhs.diagram),
    backward: startTimeline(rhs.diagram),
  }
}

export function currentSide(s: ProofSession, side: 'forward' | 'backward'): Diagram {
  return timelineCurrent(s[side])
}

export function moveSide(s: ProofSession, side: 'forward' | 'backward', cursor: number): ProofSession {
  return { ...s, [side]: moveTimeline(s[side], cursor) }
}

/** Live proof interfaces are fixed statement identities. A kernel operation
    that quotients one of them cannot leave the renderer/session holding a
    stale id; until proof steps carry an explicit boundary remap, refuse the
    step atomically and name the destroyed identity. */
function assertStatementBoundarySurvives(d: Diagram, boundary: readonly WireId[], side: 'forward' | 'backward'): void {
  for (const wire of new Set(boundary)) {
    if (d.wires[wire] === undefined) {
      throw new Error(`${side} step destroyed fixed statement-boundary wire '${wire}'; boundary-changing steps require an explicit interface remap`)
    }
  }
}

/** Apply a forward step through the kernel; refusals propagate untouched. */
export function applyForward(s: ProofSession, step: ProofStep): ProofSession {
  const next = applyStep(currentSide(s, 'forward'), step, s.ctx)
  assertStatementBoundarySurvives(next, s.lhs.boundary, 'forward')
  return {
    ...s,
    forward: appendTimeline(s.forward, step, next),
  }
}

export function undoForward(s: ProofSession): ProofSession {
  if (s.forward.cursor === 0) throw new Error('nothing to undo on the forward side')
  return moveSide(s, 'forward', s.forward.cursor - 1)
}

export function redoForward(s: ProofSession): ProofSession {
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
export function applyBackward(s: ProofSession, step: ProofStep): ProofSession {
  const g = currentSide(s, 'backward')
  const gPrime = applyStep(g, step, s.ctx, 'backward')
  assertStatementBoundarySurvives(gPrime, s.rhs.boundary, 'backward')
  return {
    ...s,
    backward: appendTimeline(s.backward, step, gPrime),
  }
}

export function undoBackward(s: ProofSession): ProofSession {
  if (s.backward.cursor === 0) throw new Error('nothing to undo on the backward side')
  return moveSide(s, 'backward', s.backward.cursor - 1)
}

export function redoBackward(s: ProofSession): ProofSession {
  if (s.backward.cursor === s.backward.states.length - 1) throw new Error('nothing to redo on the backward side')
  return moveSide(s, 'backward', s.backward.cursor + 1)
}

export function meet(s: ProofSession): boolean {
  return exploreForm(currentSide(s, 'forward')) === exploreForm(currentSide(s, 'backward'))
}

/** Both halves AS RECORDED become the theorem (caller runs checkTheorem —
    its dual replay verifies each half from its own end and the meet). */
export function assembleTheorem(s: ProofSession, name: string): Theorem {
  if (!meet(s)) throw new Error('the two sides have not met; nothing to assemble')
  return {
    name,
    lhs: s.lhs,
    rhs: s.rhs,
    steps: s.forward.steps.slice(0, s.forward.cursor),
    backSteps: s.backward.steps.slice(0, s.backward.cursor),
  }
}

/** Verify and add a finished theorem to the session context — citable from now on. */
export function adoptTheorem(s: ProofSession, thm: Theorem): ProofSession {
  if (s.ctx.theorems.has(thm.name)) {
    throw new Error(`'${thm.name}' already names a theorem in this session`)
  }
  checkTheorem(thm, s.ctx)
  const theorems = new Map(s.ctx.theorems)
  theorems.set(thm.name, thm)
  return { ...s, ctx: { theorems, relations: s.ctx.relations } }
}
