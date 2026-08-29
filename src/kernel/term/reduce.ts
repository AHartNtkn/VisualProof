import { application, bound, lambda, type Term } from './term'

/** Add an offset to every bound index at or above the cutoff. */
export function shift(offset: number, cutoff: number, term: Term): Term {
  switch (term.kind) {
    case 'bound': {
      if (term.index < cutoff) return term
      const index = term.index + offset
      if (index < 0) {
        throw new Error(`shift produced negative index ${index}; caller violated its guarantee (offset=${offset}, cutoff=${cutoff}, index=${term.index})`)
      }
      return bound(index)
    }
    case 'free': return term
    case 'lambda': return lambda(shift(offset, cutoff + 1, term.body))
    case 'application':
      return application(shift(offset, cutoff, term.fn), shift(offset, cutoff, term.argument))
  }
}

function substitute(index: number, replacement: Term, term: Term): Term {
  switch (term.kind) {
    case 'bound': return term.index === index ? replacement : term
    case 'free': return term
    case 'lambda': return lambda(substitute(index + 1, shift(1, 0, replacement), term.body))
    case 'application':
      return application(
        substitute(index, replacement, term.fn),
        substitute(index, replacement, term.argument),
      )
  }
}

/** Standard capture-avoiding de Bruijn beta substitution. */
export function betaReduce(body: Term, argument: Term): Term {
  return shift(-1, 0, substitute(0, shift(1, 0, argument), body))
}

export type PathSeg = 'body' | 'fn' | 'argument'
export type ReductionStep = {
  readonly kind: 'beta' | 'eta'
  readonly path: readonly PathSeg[]
}

/** Whether an index occurs free relative to the supplied term. */
export function hasFreeBound(index: number, term: Term): boolean {
  switch (term.kind) {
    case 'bound': return term.index === index
    case 'free': return false
    case 'lambda': return hasFreeBound(index + 1, term.body)
    case 'application':
      return hasFreeBound(index, term.fn) || hasFreeBound(index, term.argument)
  }
}

function etaContractAtRoot(term: Term): Term | null {
  if (
    term.kind === 'lambda'
    && term.body.kind === 'application'
    && term.body.argument.kind === 'bound'
    && term.body.argument.index === 0
    && !hasFreeBound(0, term.body.fn)
  ) {
    return shift(-1, 0, term.body.fn)
  }
  return null
}

export function stepNormalOrder(term: Term): { term: Term; path: PathSeg[] } | null {
  if (term.kind === 'application' && term.fn.kind === 'lambda') {
    return { term: betaReduce(term.fn.body, term.argument), path: [] }
  }
  switch (term.kind) {
    case 'lambda': {
      const result = stepNormalOrder(term.body)
      return result === null ? null : { term: lambda(result.term), path: ['body', ...result.path] }
    }
    case 'application': {
      const fn = stepNormalOrder(term.fn)
      if (fn !== null) {
        return { term: application(fn.term, term.argument), path: ['fn', ...fn.path] }
      }
      const argument = stepNormalOrder(term.argument)
      return argument === null
        ? null
        : { term: application(term.fn, argument.term), path: ['argument', ...argument.path] }
    }
    case 'bound':
    case 'free':
      return null
  }
}

export function stepEta(term: Term): { term: Term; path: PathSeg[] } | null {
  const contracted = etaContractAtRoot(term)
  if (contracted !== null) return { term: contracted, path: [] }
  switch (term.kind) {
    case 'lambda': {
      const result = stepEta(term.body)
      return result === null ? null : { term: lambda(result.term), path: ['body', ...result.path] }
    }
    case 'application': {
      const fn = stepEta(term.fn)
      if (fn !== null) {
        return { term: application(fn.term, term.argument), path: ['fn', ...fn.path] }
      }
      const argument = stepEta(term.argument)
      return argument === null
        ? null
        : { term: application(term.fn, argument.term), path: ['argument', ...argument.path] }
    }
    case 'bound':
    case 'free':
      return null
  }
}

export function applyStepAt(term: Term, step: ReductionStep): Term {
  if (step.path.length === 0) {
    if (step.kind === 'beta') {
      if (term.kind === 'application' && term.fn.kind === 'lambda') {
        return betaReduce(term.fn.body, term.argument)
      }
      if (term.kind === 'application') {
        throw new Error(`no beta redex at path []: application fn is '${term.fn.kind}', not 'lambda'`)
      }
      throw new Error(`no beta redex at path []: term head is '${term.kind}'`)
    }
    const contracted = etaContractAtRoot(term)
    if (contracted !== null) return contracted
    throw new Error('no eta redex at path []: term is not of shape \\x. f x with x unused in f')
  }

  const [segment, ...rest] = step.path
  const nested: ReductionStep = { kind: step.kind, path: rest }
  if (segment === 'body' && term.kind === 'lambda') return lambda(applyStepAt(term.body, nested))
  if (segment === 'fn' && term.kind === 'application') {
    return application(applyStepAt(term.fn, nested), term.argument)
  }
  if (segment === 'argument' && term.kind === 'application') {
    return application(term.fn, applyStepAt(term.argument, nested))
  }
  throw new Error(`invalid path segment '${segment}' into '${term.kind}' (remaining path [${step.path.join(', ')}])`)
}

export type NormalizeResult =
  | { readonly status: 'normal'; readonly term: Term; readonly path: readonly ReductionStep[] }
  | { readonly status: 'fuel-exhausted'; readonly term: Term; readonly path: readonly ReductionStep[] }

/** Fueled leftmost-outermost beta normalization followed by eta contraction. */
export function normalize(term: Term, fuel: number): NormalizeResult {
  if (!Number.isInteger(fuel) || fuel <= 0) {
    throw new Error(`fuel must be a positive integer, got ${fuel}`)
  }
  const path: ReductionStep[] = []
  let current = term
  let remaining = fuel
  for (;;) {
    const beta = stepNormalOrder(current)
    if (beta === null) break
    if (remaining === 0) return { status: 'fuel-exhausted', term: current, path }
    path.push({ kind: 'beta', path: beta.path })
    current = beta.term
    remaining--
  }
  for (;;) {
    const eta = stepEta(current)
    if (eta === null) break
    if (remaining === 0) return { status: 'fuel-exhausted', term: current, path }
    path.push({ kind: 'eta', path: eta.path })
    current = eta.term
    remaining--
  }
  return { status: 'normal', term: current, path }
}
