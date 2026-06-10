import type { Term } from './term'
import { bvar, lam, app } from './term'

/** Add d to every bvar index >= cutoff. d may be negative (caller guarantees no index goes negative). */
export function shift(d: number, cutoff: number, t: Term): Term {
  switch (t.kind) {
    case 'bvar': {
      if (t.index < cutoff) return t
      const next = t.index + d
      // Unreachable from betaReduce (substitution removes all index-0 occurrences
      // before the decrement); guards direct callers of shift(-d, ...).
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

export type PathSeg = 'body' | 'fn' | 'arg'
export type ReductionStep = { readonly kind: 'beta' | 'eta'; readonly path: readonly PathSeg[] }

/** True iff bvar with the given index occurs free in t. */
export function hasFreeBVar(index: number, t: Term): boolean {
  switch (t.kind) {
    case 'bvar': return t.index === index
    case 'lam': return hasFreeBVar(index + 1, t.body)
    case 'app': return hasFreeBVar(index, t.fn) || hasFreeBVar(index, t.arg)
    case 'port':
    case 'const':
      return false
  }
}

/**
 * One leftmost-outermost beta step. Returns the reduced term and the redex path,
 * or null if t is in beta-normal form. Normal order finds a normal form whenever
 * one exists, which is why it is the kernel's strategy.
 */
export function stepNormalOrder(t: Term): { term: Term; path: PathSeg[] } | null {
  if (t.kind === 'app' && t.fn.kind === 'lam') {
    return { term: betaReduce(t.fn.body, t.arg), path: [] }
  }
  switch (t.kind) {
    case 'lam': {
      const r = stepNormalOrder(t.body)
      return r === null ? null : { term: lam(r.term), path: ['body', ...r.path] }
    }
    case 'app': {
      const rf = stepNormalOrder(t.fn)
      if (rf !== null) return { term: app(rf.term, t.arg), path: ['fn', ...rf.path] }
      const ra = stepNormalOrder(t.arg)
      if (ra !== null) return { term: app(t.fn, ra.term), path: ['arg', ...ra.path] }
      return null
    }
    case 'bvar':
    case 'port':
    case 'const':
      return null
  }
}

/** Apply one named reduction step at an explicit path. Throws specifically when the path or redex is invalid. */
export function applyStepAt(t: Term, step: ReductionStep): Term {
  const fmt = (p: readonly PathSeg[]) => `[${p.join(', ')}]`
  if (step.path.length === 0) {
    if (step.kind === 'beta') {
      if (t.kind === 'app' && t.fn.kind === 'lam') return betaReduce(t.fn.body, t.arg)
      if (t.kind === 'app') {
        throw new Error(`no beta redex at path []: app fn is '${t.fn.kind}', not 'lam'`)
      }
      throw new Error(`no beta redex at path []: term head is '${t.kind}'`)
    }
    // eta: \x. f x with x not free in f  →  shift(-1, 0, f)
    if (t.kind === 'lam' && t.body.kind === 'app'
      && t.body.arg.kind === 'bvar' && t.body.arg.index === 0
      && !hasFreeBVar(0, t.body.fn)) {
      return shift(-1, 0, t.body.fn)
    }
    throw new Error(`no eta redex at path []: term is not of shape \\x. f x with x unused in f`)
  }
  const [seg, ...rest] = step.path
  const sub: ReductionStep = { kind: step.kind, path: rest }
  if (seg === 'body' && t.kind === 'lam') return lam(applyStepAt(t.body, sub))
  if (seg === 'fn' && t.kind === 'app') return app(applyStepAt(t.fn, sub), t.arg)
  if (seg === 'arg' && t.kind === 'app') return app(t.fn, applyStepAt(t.arg, sub))
  throw new Error(`invalid path segment '${seg}' into '${t.kind}' (remaining path ${fmt(step.path)})`)
}

export type NormalizeResult =
  | { status: 'normal'; term: Term; path: ReductionStep[] }
  | { status: 'fuel-exhausted'; term: Term; path: ReductionStep[] }

/** One leftmost-outermost eta step, or null if eta-normal. */
export function stepEta(t: Term): { term: Term; path: PathSeg[] } | null {
  if (t.kind === 'lam' && t.body.kind === 'app'
    && t.body.arg.kind === 'bvar' && t.body.arg.index === 0
    && !hasFreeBVar(0, t.body.fn)) {
    return { term: shift(-1, 0, t.body.fn), path: [] }
  }
  switch (t.kind) {
    case 'lam': {
      const r = stepEta(t.body)
      return r === null ? null : { term: lam(r.term), path: ['body', ...r.path] }
    }
    case 'app': {
      const rf = stepEta(t.fn)
      if (rf !== null) return { term: app(rf.term, t.arg), path: ['fn', ...rf.path] }
      const ra = stepEta(t.arg)
      if (ra !== null) return { term: app(t.fn, ra.term), path: ['arg', ...ra.path] }
      return null
    }
    case 'bvar':
    case 'port':
    case 'const':
      return null
  }
}

/**
 * Fueled βη-normalization: normal-order beta to beta-normal form, then eta
 * contraction to fixpoint. Complete for finding βη-normal forms: normal order
 * finds the beta-normal form whenever one exists, and by eta-postponement the
 * eta steps can always be done after the beta steps. Each step consumes one
 * fuel unit; constants are opaque here (unfolding is the explicit rule 7).
 */
export function normalize(t: Term, fuel: number): NormalizeResult {
  if (!Number.isInteger(fuel) || fuel <= 0) {
    throw new Error(`fuel must be a positive integer, got ${fuel}`)
  }
  const path: ReductionStep[] = []
  let cur = t
  let remaining = fuel
  for (;;) {
    if (remaining === 0) return { status: 'fuel-exhausted', term: cur, path }
    const b = stepNormalOrder(cur)
    if (b === null) break
    path.push({ kind: 'beta', path: b.path })
    cur = b.term
    remaining--
  }
  for (;;) {
    if (remaining === 0) return { status: 'fuel-exhausted', term: cur, path }
    const e = stepEta(cur)
    if (e === null) break
    path.push({ kind: 'eta', path: e.path })
    cur = e.term
    remaining--
  }
  return { status: 'normal', term: cur, path }
}
