import type { Term } from './term'
import { termEq } from './term'
import type { ReductionStep } from './reduce'
import { applyStepAt } from './reduce'

/**
 * A conversion certificate: explicit βη reduction paths from each side to a
 * common reduct (sound by Church–Rosser). This is the artifact stored in proof
 * steps so replay never re-searches: checking is mechanical and fuel-free.
 */
export type ConversionCertificate = {
  readonly leftSteps: readonly ReductionStep[]
  readonly rightSteps: readonly ReductionStep[]
}

export type ConversionCheck =
  | { ok: true; meet: Term }
  | { ok: false; reason: string }

export function checkConversion(left: Term, right: Term, cert: ConversionCertificate): ConversionCheck {
  let l = left
  for (const [i, step] of cert.leftSteps.entries()) {
    try {
      l = applyStepAt(l, step)
    } catch (e) {
      return { ok: false, reason: `left step ${i} is invalid: ${e instanceof Error ? e.message : String(e)}` }
    }
  }
  let r = right
  for (const [i, step] of cert.rightSteps.entries()) {
    try {
      r = applyStepAt(r, step)
    } catch (e) {
      return { ok: false, reason: `right step ${i} is invalid: ${e instanceof Error ? e.message : String(e)}` }
    }
  }
  if (!termEq(l, r)) {
    return { ok: false, reason: 'the two reduction paths do not meet at a common term' }
  }
  return { ok: true, meet: l }
}
