import type { Diagram, WireId } from '../kernel/diagram/diagram'
import type { ProofContext, ProofStep } from '../kernel/proof/step'
import { replayProof } from '../kernel/proof/step'
import type { Theorem } from '../kernel/proof/theorem'

/**
 * A stepper over a verified theorem's recorded derivation. Step k is the
 * diagram after k rule applications: k=0 is the left-hand side, k=stepCount is
 * the replayed right-hand side. The boundary wires (lhs.boundary) survive every
 * step by checkTheorem's per-step invariant, so a single boundary serves the
 * whole replay — the caller pins frame exits with it at any k.
 *
 * Nothing here is a re-verification: the theorem was checked when it entered the
 * context. Replay just re-runs the same deterministic appliers to surface the
 * intermediate diagrams the proof passed through, for the view to animate.
 */
export type Replay = {
  readonly stepCount: number
  readonly steps: readonly ProofStep[]
  /** Diagram after k steps (0 ≤ k ≤ stepCount). */
  diagramAt(k: number): Diagram
  /** Rule name of step k (1-based); '' at k=0, which applied no rule. */
  labelAt(k: number): string
  readonly boundary: readonly WireId[]
}

export function mkReplay(thm: Theorem, ctx: ProofContext): Replay {
  const n = thm.steps.length
  // cache[k] = diagram after k steps; index 0 is the lhs, always present.
  const cache: Diagram[] = [thm.lhs.diagram]

  const inRange = (k: number): boolean => Number.isInteger(k) && k >= 0 && k <= n

  // Fill cache[cache.length .. k] by replaying ONLY the uncached suffix from the
  // last cached diagram — replayProof's onStep hands us each intermediate. A
  // monotone walk therefore applies every step exactly once across all calls.
  const ensure = (k: number): void => {
    if (k < cache.length) return
    const have = cache.length - 1
    replayProof(cache[have]!, thm.steps.slice(have, k), ctx, (d, i) => {
      cache[have + 1 + i] = d
    })
  }

  return {
    stepCount: n,
    steps: thm.steps,
    boundary: thm.lhs.boundary,
    diagramAt(k: number): Diagram {
      if (!inRange(k)) throw new Error(`replay step ${k} is out of range [0, ${n}]`)
      ensure(k)
      return cache[k]!
    },
    labelAt(k: number): string {
      if (!inRange(k)) throw new Error(`replay step ${k} is out of range [0, ${n}]`)
      return k === 0 ? '' : thm.steps[k - 1]!.rule
    },
  }
}
