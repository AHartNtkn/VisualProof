import type { Term } from './term'
import { termEq } from './term'
import type { ReductionStep } from './reduce'
import { applyStepAt, stepEta, stepNormalOrder } from './reduce'

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
  | { readonly ok: true; readonly meet: Term }
  | { readonly ok: false; readonly reason: string }

export type NormalSeparationCertificate = {
  readonly firstSteps: readonly ReductionStep[]
  readonly secondSteps: readonly ReductionStep[]
}

export type NormalSeparationCheck =
  | { readonly ok: true; readonly firstNormal: Term; readonly secondNormal: Term }
  | { readonly ok: false; readonly reason: string }

function replayPath(
  start: Term,
  steps: readonly ReductionStep[],
  side: 'first' | 'second' | 'left' | 'right',
): { readonly ok: true; readonly term: Term } | { readonly ok: false; readonly reason: string } {
  let term = start
  for (const [index, step] of steps.entries()) {
    try {
      term = applyStepAt(term, step)
    } catch (error) {
      return {
        ok: false,
        reason: `${side} step ${index} is invalid: ${error instanceof Error ? error.message : String(error)}`,
      }
    }
  }
  return { ok: true, term }
}

export function checkNormalSeparation(
  first: Term,
  second: Term,
  certificate: NormalSeparationCertificate,
): NormalSeparationCheck {
  const firstResult = replayPath(first, certificate.firstSteps, 'first')
  if (!firstResult.ok) return firstResult

  const secondResult = replayPath(second, certificate.secondSteps, 'second')
  if (!secondResult.ok) return secondResult

  if (stepNormalOrder(firstResult.term) !== null || stepEta(firstResult.term) !== null) {
    return { ok: false, reason: 'first reduction path does not end in beta-eta normal form' }
  }
  if (stepNormalOrder(secondResult.term) !== null || stepEta(secondResult.term) !== null) {
    return { ok: false, reason: 'second reduction path does not end in beta-eta normal form' }
  }
  if (termEq(firstResult.term, secondResult.term)) {
    return { ok: false, reason: 'the two reduction paths end in the same normal form' }
  }
  return { ok: true, firstNormal: firstResult.term, secondNormal: secondResult.term }
}

export function checkConversion(left: Term, right: Term, cert: ConversionCertificate): ConversionCheck {
  const leftResult = replayPath(left, cert.leftSteps, 'left')
  if (!leftResult.ok) return leftResult

  const rightResult = replayPath(right, cert.rightSteps, 'right')
  if (!rightResult.ok) return rightResult

  if (!termEq(leftResult.term, rightResult.term)) {
    return { ok: false, reason: 'the two reduction paths do not meet at a common term' }
  }
  return { ok: true, meet: leftResult.term }
}
