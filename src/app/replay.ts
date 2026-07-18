import type { Diagram, WireId } from '../kernel/diagram/diagram'
import { transportBoundary } from '../kernel/proof/step'
import type { ProofContext, ProofStep } from '../kernel/proof/step'
import { replayActions } from '../kernel/proof/action'
import type { Theorem } from '../kernel/proof/theorem'

/**
 * A scrubber over a verified theorem's recorded derivation. Position k is the
 * diagram after k actions: k=0 is the left-hand side, k=actionCount is
 * the replayed right-hand side. Each position carries the boundary produced by
 * the same per-step semantic interface that checkTheorem verified.
 *
 * Nothing here is a re-verification: the theorem was checked when it entered the
 * context. Replay just re-runs the same deterministic appliers to surface the
 * intermediate diagrams the proof passed through, for the view to animate.
 */
export type Replay = {
  readonly actionCount: number
  readonly actions: Theorem['actions']
  /** Diagram after k actions (0 ≤ k ≤ actionCount). */
  diagramAt(k: number): Diagram
  /** Action label at k (1-based); '' at k=0, which applied no action. */
  labelAt(k: number): string
  stepsAt(k: number): readonly ProofStep[]
  boundaryAt(k: number): readonly WireId[]
}

export function mkReplay(thm: Theorem, ctx: ProofContext): Replay {
  const n = thm.actions.length
  // cache[k] = diagram after k steps; index 0 is the lhs, always present.
  const cache: Diagram[] = [thm.lhs.diagram]
  const boundaries: (readonly WireId[])[] = [thm.lhs.boundary]

  const inRange = (k: number): boolean => Number.isInteger(k) && k >= 0 && k <= n

  // Fill cache[cache.length .. k] by replaying ONLY the uncached suffix from the
  // last cached diagram — replayProof's onStep hands us each intermediate. A
  // monotone walk therefore applies every step exactly once across all calls.
  const ensure = (k: number): void => {
    if (k < cache.length) return
    const have = cache.length - 1
    let boundary = boundaries[have]!
    replayActions(cache[have]!, thm.actions.slice(have, k), ctx, (d, actionIndex, stepIndex, receipt) => {
      const mapped = transportBoundary(receipt.interface, boundary)
      if (mapped === undefined) throw new Error('verified theorem replay produced an untransportable boundary')
      boundary = mapped
      if (stepIndex === thm.actions[have + actionIndex]!.steps.length - 1) {
        cache[have + 1 + actionIndex] = d
        boundaries[have + 1 + actionIndex] = boundary
      }
    })
  }

  return {
    actionCount: n,
    actions: thm.actions,
    diagramAt(k: number): Diagram {
      if (!inRange(k)) throw new Error(`replay step ${k} is out of range [0, ${n}]`)
      ensure(k)
      return cache[k]!
    },
    boundaryAt(k: number): readonly WireId[] {
      if (!inRange(k)) throw new Error(`replay step ${k} is out of range [0, ${n}]`)
      ensure(k)
      return boundaries[k]!
    },
    labelAt(k: number): string {
      if (!inRange(k)) throw new Error(`replay step ${k} is out of range [0, ${n}]`)
      return k === 0 ? '' : thm.actions[k - 1]!.label
    },
    stepsAt(k: number): readonly ProofStep[] {
      if (!inRange(k)) throw new Error(`replay action ${k} is out of range [0, ${n}]`)
      return k === 0 ? [] : thm.actions[k - 1]!.steps
    },
  }
}
