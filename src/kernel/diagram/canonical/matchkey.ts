import type { Term } from '../../term/term'
import { app, assertWellFormedTerm, bvar, freePorts, lam, termEq } from '../../term/term'
import { normalize } from '../../term/reduce'
import { DiagramError } from '../diagram'

/**
 * Close a term over its free ports in first-occurrence order: port i becomes
 * the i-th outermost lambda. Two nodes denote the same positional relation iff
 * their closures are beta-eta-convertible closed terms. Closing FIRST fixes
 * the arity, so normalization cannot drop a port out from under the wiring.
 */
export function closeOverPorts(t: Term): Term {
  assertWellFormedTerm(t)
  const order = freePorts(t)
  const n = order.length
  const index = new Map(order.map((name, i) => [name, i]))
  const walk = (u: Term, depth: number): Term => {
    switch (u.kind) {
      case 'port': {
        // index.get cannot miss: freePorts collects every port name
        const i = index.get(u.name)!
        // innermost closure lambda is p(n-1) at distance `depth`; p(i) sits
        // (n-1-i) binders further out
        return bvar(depth + (n - 1 - i))
      }
      case 'bvar': return bvar(u.index)
      case 'lam': return lam(walk(u.body, depth + 1))
      case 'app': return app(walk(u.fn, depth), walk(u.arg, depth))
    }
  }
  let closed = walk(t, 0)
  for (let i = 0; i < n; i++) closed = lam(closed)
  return closed
}

export type NodeMatchVerdict =
  | { readonly status: 'match' }
  | { readonly status: 'no-match' }
  | { readonly status: 'undecided'; readonly detail: string }

/**
 * Do two term nodes denote the same positional relation, modulo beta-eta?
 * Decided by bounded normalization of the port closures. Fuel exhaustion is a
 * loud 'undecided' verdict naming the side — never a silent answer; the
 * relation is undecidable in general (spec §3.7).
 */
export function termsMatchModuloBetaEta(a: Term, b: Term, fuel: number): NodeMatchVerdict {
  if (!Number.isInteger(fuel) || fuel <= 0) {
    throw new DiagramError(`fuel must be a positive integer, got ${fuel}`)
  }
  if (freePorts(a).length !== freePorts(b).length) return { status: 'no-match' }
  const ca = closeOverPorts(a)
  const cb = closeOverPorts(b)
  // Sound shortcut, not a heuristic: structural equality of closures implies
  // convertibility by reflexivity — and avoids spurious 'undecided' verdicts
  // on identical non-normalizing terms.
  if (termEq(ca, cb)) return { status: 'match' }
  const na = normalize(ca, fuel)
  if (na.status === 'fuel-exhausted') {
    return { status: 'undecided', detail: `left closure did not normalize within ${fuel} steps` }
  }
  const nb = normalize(cb, fuel)
  if (nb.status === 'fuel-exhausted') {
    return { status: 'undecided', detail: `right closure did not normalize within ${fuel} steps` }
  }
  return termEq(na.term, nb.term) ? { status: 'match' } : { status: 'no-match' }
}
