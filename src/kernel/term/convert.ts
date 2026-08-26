import type { ConversionCertificate } from './certificate'
import { normalize } from './reduce'
import { termEq, type Term } from './term'

export type ConvertibleResult =
  | { readonly status: 'convertible'; readonly certificate: ConversionCertificate }
  | { readonly status: 'not-convertible' }
  | { readonly status: 'fuel-exhausted'; readonly detail: string }

/** Fueled interactive search; replay uses the returned fuel-free certificate. */
export function convertible(left: Term, right: Term, fuel: number): ConvertibleResult {
  const leftNormal = normalize(left, fuel)
  if (leftNormal.status === 'fuel-exhausted') {
    return { status: 'fuel-exhausted', detail: `left term did not normalize within ${fuel} steps` }
  }
  const rightNormal = normalize(right, fuel)
  if (rightNormal.status === 'fuel-exhausted') {
    return { status: 'fuel-exhausted', detail: `right term did not normalize within ${fuel} steps` }
  }
  if (termEq(leftNormal.term, rightNormal.term)) {
    return {
      status: 'convertible',
      certificate: { leftSteps: leftNormal.path, rightSteps: rightNormal.path },
    }
  }
  return { status: 'not-convertible' }
}
