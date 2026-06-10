import type { Term } from './term'
import { bvar, lam, app } from './term'

/** Add d to every bvar index >= cutoff. d may be negative (caller guarantees no index goes negative). */
export function shift(d: number, cutoff: number, t: Term): Term {
  switch (t.kind) {
    case 'bvar': {
      if (t.index < cutoff) return t
      const next = t.index + d
      if (next < 0) {
        throw new Error(`shift produced negative index ${next}; caller violated its guarantee (d=${d}, cutoff=${cutoff}, index=${t.index})`)
      }
      return bvar(next)
    }
    case 'lam': return lam(shift(d, cutoff + 1, t.body))
    case 'app': return app(shift(d, cutoff, t.fn), shift(d, cutoff, t.arg))
    case 'port':
    case 'const':
      return t
  }
}

/** Substitute s for bvar j in t, shifting s under binders. */
function subst(j: number, s: Term, t: Term): Term {
  switch (t.kind) {
    case 'bvar': return t.index === j ? s : t
    case 'lam': return lam(subst(j + 1, shift(1, 0, s), t.body))
    case 'app': return app(subst(j, s, t.fn), subst(j, s, t.arg))
    case 'port':
    case 'const':
      return t
  }
}

/** The body of a redex (\. body) applied to arg: shift(-1) ∘ subst(0, shift(1) arg). Standard de Bruijn beta. */
export function betaReduce(body: Term, arg: Term): Term {
  return shift(-1, 0, subst(0, shift(1, 0, arg), body))
}
