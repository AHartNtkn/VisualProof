import type { Diagram, WireId } from '../kernel/diagram/diagram'
import type { ProofContext, ProofStep } from '../kernel/proof/step'
import { replayActions } from '../kernel/proof/action'
import type { Theorem } from '../kernel/proof/theorem'

/**
 * A scrubber over a verified theorem's recorded derivation. Position k is the
 * diagram after k actions: k=0 is the left-hand side, k=actionCount is
 * the replayed right-hand side. The boundary wires (lhs.boundary) survive every
 * step by checkTheorem's per-step invariant, so a single boundary serves the
 * whole replay — the caller pins frame exits with it at any k.
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
  readonly boundary: readonly WireId[]
}

export function mkReplay(thm: Theorem, ctx: ProofContext): Replay {
  const n = thm.actions.length
  // cache[k] = diagram after k steps; index 0 is the lhs, always present.
  const cache: Diagram[] = [thm.lhs.diagram]

  const inRange = (k: number): boolean => Number.isInteger(k) && k >= 0 && k <= n

  // Fill cache[cache.length .. k] by replaying ONLY the uncached suffix from the
  // last cached diagram — replayProof's onStep hands us each intermediate. A
  // monotone walk therefore applies every step exactly once across all calls.
  const ensure = (k: number): void => {
    if (k < cache.length) return
    const have = cache.length - 1
    replayActions(cache[have]!, thm.actions.slice(have, k), ctx, (d, actionIndex, stepIndex) => {
      if (stepIndex === thm.actions[have + actionIndex]!.steps.length - 1) cache[have + 1 + actionIndex] = d
    })
  }

  return {
    actionCount: n,
    actions: thm.actions,
    boundary: thm.lhs.boundary,
    diagramAt(k: number): Diagram {
      if (!inRange(k)) throw new Error(`replay step ${k} is out of range [0, ${n}]`)
      ensure(k)
      return cache[k]!
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
