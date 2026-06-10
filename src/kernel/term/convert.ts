import type { Term } from './term'
import { termEq } from './term'
import { normalize } from './reduce'
import type { ConversionCertificate } from './certificate'

export type ConvertibleResult =
  | { status: 'convertible'; certificate: ConversionCertificate }
  | { status: 'not-convertible' }
  | { status: 'fuel-exhausted'; detail: string }

/**
 * Interactive equality: normalize both sides under the fuel budget and compare.
 * - Both normalize and meet: convertible, with the reduction paths as the certificate.
 * - Both normalize and differ: definitively not convertible (normal forms are unique).
 * - Either runs out of fuel: reported as such — the kernel never guesses.
 * Fuel affects this interactive search only; stored proofs carry certificates (§3.7 of the spec).
 * Constants are opaque at this layer; definitional unfolding is rule 7, a separate layer.
 * If left normalizes, right exhaustion is reported independently; when both sides would
 * exhaust, only the left is named — call normalize directly to diagnose both.
 */
export function convertible(left: Term, right: Term, fuel: number): ConvertibleResult {
  const l = normalize(left, fuel)
  if (l.status === 'fuel-exhausted') {
    return { status: 'fuel-exhausted', detail: `left term did not normalize within ${fuel} steps` }
  }
  const r = normalize(right, fuel)
  if (r.status === 'fuel-exhausted') {
    return { status: 'fuel-exhausted', detail: `right term did not normalize within ${fuel} steps` }
  }
  if (termEq(l.term, r.term)) {
    return { status: 'convertible', certificate: { leftSteps: l.path, rightSteps: r.path } }
  }
  return { status: 'not-convertible' }
}
