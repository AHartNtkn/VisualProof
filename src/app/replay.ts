import type { Diagram, WireId } from '../kernel/diagram/diagram'
import { exploreForm } from '../kernel/diagram/canonical/explore'
import { transportBoundary } from '../kernel/proof/step'
import type { ProofContext } from '../kernel/proof/context'
import { assertProofContext } from '../kernel/proof/context'
import type { ProofStep } from '../kernel/proof/step'
import { applyAction, type ProofAction } from '../kernel/proof/action'

/**
 * A scrubber over both halves of a verified theorem's recorded derivation.
 * Position zero is the exact declared lhs unless all landmarks coincide;
 * meetingIndex is the verified meeting form, and actionCount is always the
 * exact declared rhs. At a shared meeting/RHS index, exact RHS representation
 * takes precedence over the canonically equivalent computed meeting object.
 *
 * Nothing here is a re-verification: the theorem was checked when it entered the
 * context. Replay re-runs each half from its declared endpoint with its recorded
 * orientation, then presents the backward trace in reverse display order.
 */
export type ReplayHalf = 'forward' | 'backward'

export type ReplayTransition = {
  readonly half: ReplayHalf
  readonly action: ProofAction
  /** The diagram on which this action was actually verified and replayed. */
  readonly appliedFrom: Diagram
  readonly orientation: 'forward' | 'backward'
}

export type Replay = {
  readonly actionCount: number
  readonly meetingIndex: number
  /** Presentation-order actions, one for each displayed transition. */
  readonly actions: readonly ProofAction[]
  readonly transitions: readonly ReplayTransition[]
  /** Diagram after k actions (0 ≤ k ≤ actionCount). */
  diagramAt(k: number): Diagram
  /** Action label at k (1-based); '' at k=0, which applied no action. */
  labelAt(k: number): string
  stepsAt(k: number): readonly ProofStep[]
  boundaryAt(k: number): readonly WireId[]
}

export function mkReplay(name: string, ctx: ProofContext): Replay {
  assertProofContext(ctx)
  const thm = ctx.theorems.get(name)
  if (thm === undefined) throw new Error(`unknown certified theorem '${name}'`)

  const replayHalf = (
    initial: Diagram,
    initialBoundary: readonly WireId[],
    actions: readonly ProofAction[],
    half: ReplayHalf,
  ): {
    readonly states: readonly Diagram[]
    readonly boundaries: readonly (readonly WireId[])[]
    readonly transitions: readonly ReplayTransition[]
  } => {
    const states: Diagram[] = [initial]
    const boundaries: (readonly WireId[])[] = [initialBoundary]
    const transitions: ReplayTransition[] = []
    let current = initial
    let boundary = initialBoundary
    for (const action of actions) {
      const appliedFrom = current
      current = applyAction(current, action, ctx, half, (_diagram, _stepIndex, receipt) => {
        const mapped = transportBoundary(receipt.interface, boundary)
        if (mapped === undefined) throw new Error('verified theorem replay produced an untransportable boundary')
        boundary = mapped
      })
      states.push(current)
      boundaries.push(boundary)
      transitions.push({ half, action, appliedFrom, orientation: half })
    }
    return {
      states: Object.freeze(states),
      boundaries: Object.freeze(boundaries),
      transitions: Object.freeze(transitions),
    }
  }

  const forward = replayHalf(thm.lhs.diagram, thm.lhs.boundary, thm.actions, 'forward')
  const backward = replayHalf(
    thm.rhs.diagram,
    thm.rhs.boundary,
    thm.backActions ?? [],
    'backward',
  )
  const forwardMeet = forward.states.at(-1)!
  const backwardMeet = backward.states.at(-1)!
  const forwardMeetBoundary = forward.boundaries.at(-1)!
  const backwardMeetBoundary = backward.boundaries.at(-1)!
  if (
    exploreForm(forwardMeet, forwardMeetBoundary)
    !== exploreForm(backwardMeet, backwardMeetBoundary)
  ) {
    throw new Error(`verified theorem replay '${name}' has proof halves that do not meet`)
  }

  // Backward execution is rhs -> ... -> meet. Presentation is meet -> ... -> rhs,
  // so reverse the already-verified states/transitions; never reapply those
  // actions as forward inference.
  const backwardDisplayStates = backward.states.slice(0, -1).reverse()
  const backwardDisplayBoundaries = backward.boundaries.slice(0, -1).reverse()
  const transitions = Object.freeze([
    ...forward.transitions,
    ...backward.transitions.slice().reverse(),
  ])
  const actions = Object.freeze(transitions.map(({ action }) => action))
  const meetingIndex = thm.actions.length
  const n = transitions.length
  const displayStates = [...forward.states, ...backwardDisplayStates]
  const displayBoundaries = [...forward.boundaries, ...backwardDisplayBoundaries]
  if (meetingIndex === n) {
    displayStates[n] = thm.rhs.diagram
    displayBoundaries[n] = thm.rhs.boundary
  }
  const states = Object.freeze(displayStates)
  const boundaries = Object.freeze(displayBoundaries)
  const inRange = (k: number): boolean => Number.isInteger(k) && k >= 0 && k <= n

  return {
    actionCount: n,
    meetingIndex,
    actions,
    transitions,
    diagramAt(k: number): Diagram {
      if (!inRange(k)) throw new Error(`replay step ${k} is out of range [0, ${n}]`)
      return states[k]!
    },
    boundaryAt(k: number): readonly WireId[] {
      if (!inRange(k)) throw new Error(`replay step ${k} is out of range [0, ${n}]`)
      return boundaries[k]!
    },
    labelAt(k: number): string {
      if (!inRange(k)) throw new Error(`replay step ${k} is out of range [0, ${n}]`)
      if (k === 0) return ''
      const transition = transitions[k - 1]!
      return `${transition.half} · ${transition.action.label}`
    },
    stepsAt(k: number): readonly ProofStep[] {
      if (!inRange(k)) throw new Error(`replay action ${k} is out of range [0, ${n}]`)
      return k === 0 ? [] : transitions[k - 1]!.action.steps
    },
  }
}
