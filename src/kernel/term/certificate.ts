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
  for (let i = 0; i < cert.leftSteps.length; i++) {
    try {
      l = applyStepAt(l, cert.leftSteps[i]!)
    } catch (e) {
      return { ok: false, reason: `left step ${i} is invalid: ${(e as Error).message}` }
    }
  }
  let r = right
  for (let i = 0; i < cert.rightSteps.length; i++) {
    try {
      r = applyStepAt(r, cert.rightSteps[i]!)
    } catch (e) {
      return { ok: false, reason: `right step ${i} is invalid: ${(e as Error).message}` }
    }
  }
  if (!termEq(l, r)) {
    return { ok: false, reason: 'the two reduction paths do not meet at a common term' }
  }
  return { ok: true, meet: l }
}
