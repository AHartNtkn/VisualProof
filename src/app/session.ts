import type { Diagram, WireId } from '../kernel/diagram/diagram'
import type { DiagramWithBoundary } from '../kernel/diagram/boundary'
import { exploreForm } from '../kernel/diagram/canonical/explore'
import type { ProofContext, ProofStep } from '../kernel/proof/step'
import { applyStep } from '../kernel/proof/step'
import type { Theorem } from '../kernel/proof/theorem'
import { checkTheorem } from '../kernel/proof/theorem'

export type Side = {
  readonly current: Diagram
  readonly steps: readonly ProofStep[]
  readonly history: readonly Diagram[]
}

export type ProofSession = {
  readonly lhs: DiagramWithBoundary
  readonly rhs: DiagramWithBoundary
  readonly ctx: ProofContext
  readonly forward: Side
  /** The backward side records the user's flip-gated steps AS GIVEN; they
      replay from the rhs at declaration (checkTheorem's dual replay). */
  readonly backward: Side
}

export type TrackDirection = 'forward' | 'backward'

/** One-origin proving: the current sheet is the fixed end and the other end is
    derived by the user's track. This is the ordinary proof workflow; a
    two-ended ProofSession is reserved for an explicitly fixed statement. */
export type TrackSession = {
  readonly origin: DiagramWithBoundary
  readonly direction: TrackDirection
  readonly ctx: ProofContext
  readonly current: Diagram
  readonly steps: readonly ProofStep[]
  readonly history: readonly Diagram[]
}

export function startTrack(origin: DiagramWithBoundary, direction: TrackDirection, ctx: ProofContext): TrackSession {
  return { origin, direction, ctx, current: origin.diagram, steps: [], history: [] }
}

export function trackBoundary(track: TrackSession): readonly WireId[] {
  return track.origin.boundary.filter((wire) => track.current.wires[wire] !== undefined)
}

export function applyTrack(track: TrackSession, step: ProofStep): TrackSession {
  const next = track.direction === 'forward'
    ? applyStep(track.current, step, track.ctx)
    : applyStep(track.current, step, track.ctx, 'backward')
  return {
    ...track,
    current: next,
    steps: [...track.steps, step],
    history: [...track.history, track.current],
  }
}

export function undoTrack(track: TrackSession): TrackSession {
  const previous = track.history.at(-1)
  if (previous === undefined) throw new Error(`nothing to undo on the ${track.direction} track`)
  return {
    ...track,
    current: previous,
    steps: track.steps.slice(0, -1),
    history: track.history.slice(0, -1),
  }
}

export function declareTrack(track: TrackSession, name: string): Theorem {
  const current = { diagram: track.current, boundary: trackBoundary(track) }
  const theorem: Theorem = track.direction === 'forward'
    ? { name, lhs: track.origin, rhs: current, steps: [...track.steps] }
    : { name, lhs: current, rhs: track.origin, steps: [], backSteps: [...track.steps] }
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
    forward: { current: lhs.diagram, steps: [], history: [] },
    backward: { current: rhs.diagram, steps: [], history: [] },
  }
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
  const next = applyStep(s.forward.current, step, s.ctx)
  assertStatementBoundarySurvives(next, s.lhs.boundary, 'forward')
  return {
    ...s,
    forward: {
      current: next,
      steps: [...s.forward.steps, step],
      history: [...s.forward.history, s.forward.current],
    },
  }
}

export function undoForward(s: ProofSession): ProofSession {
  const history = s.forward.history
  if (history.length === 0) throw new Error('nothing to undo on the forward side')
  return {
    ...s,
    forward: {
      current: history[history.length - 1]!,
      steps: s.forward.steps.slice(0, -1),
      history: history.slice(0, -1),
    },
  }
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
  const g = s.backward.current
  const gPrime = applyStep(g, step, s.ctx, 'backward')
  assertStatementBoundarySurvives(gPrime, s.rhs.boundary, 'backward')
  return {
    ...s,
    backward: {
      current: gPrime,
      steps: [...s.backward.steps, step],
      history: [...s.backward.history, g],
    },
  }
}

export function undoBackward(s: ProofSession): ProofSession {
  const history = s.backward.history
  if (history.length === 0) throw new Error('nothing to undo on the backward side')
  return {
    ...s,
    backward: {
      current: history[history.length - 1]!,
      steps: s.backward.steps.slice(0, -1),
      history: history.slice(0, -1),
    },
  }
}

export function meet(s: ProofSession): boolean {
  return exploreForm(s.forward.current) === exploreForm(s.backward.current)
}

/** Both halves AS RECORDED become the theorem (caller runs checkTheorem —
    its dual replay verifies each half from its own end and the meet). */
export function assembleTheorem(s: ProofSession, name: string): Theorem {
  if (!meet(s)) throw new Error('the two sides have not met; nothing to assemble')
  return {
    name,
    lhs: s.lhs,
    rhs: s.rhs,
    steps: [...s.forward.steps],
    backSteps: [...s.backward.steps],
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
