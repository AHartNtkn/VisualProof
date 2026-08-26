export type Term =
  | { readonly kind: 'bound'; readonly index: number }
  | { readonly kind: 'free'; readonly slot: number }
  | { readonly kind: 'lambda'; readonly body: Term }
  | { readonly kind: 'application'; readonly fn: Term; readonly argument: Term }

export function bound(index: number): Term {
  if (!Number.isSafeInteger(index) || index < 0) {
    throw new Error(`bound index must be a non-negative safe integer, got ${index} (negative, fractional, or unsafely large indices are meaningless)`)
  }
  return { kind: 'bound', index }
}

export function free(slot: number): Term {
  if (!Number.isSafeInteger(slot) || slot < 0) {
    throw new Error(`free slot must be a non-negative safe integer, got ${slot} (negative, fractional, or unsafely large slots are meaningless)`)
  }
  return { kind: 'free', slot }
}

export function lambda(body: Term): Term {
  return { kind: 'lambda', body }
}

export function application(fn: Term, argument: Term): Term {
  return { kind: 'application', fn, argument }
}

export function termEq(left: Term, right: Term): boolean {
  if (left.kind !== right.kind) return false
  switch (left.kind) {
    case 'bound': return left.index === (right as Extract<Term, { kind: 'bound' }>).index
    case 'free': return left.slot === (right as Extract<Term, { kind: 'free' }>).slot
    case 'lambda': return termEq(left.body, (right as Extract<Term, { kind: 'lambda' }>).body)
    case 'application': {
      const applicationRight = right as Extract<Term, { kind: 'application' }>
      return termEq(left.fn, applicationRight.fn) && termEq(left.argument, applicationRight.argument)
    }
  }
}

/** The smallest interface arity containing every free slot used by the term. */
export function freeArity(term: Term): number {
  switch (term.kind) {
    case 'bound': return 0
    case 'free': return term.slot + 1
    case 'lambda': return freeArity(term.body)
    case 'application': return Math.max(freeArity(term.fn), freeArity(term.argument))
  }
}

/** Validate structural literals, binder scope, and (when supplied) the free interface. */
export function assertWellFormedTerm(term: Term, interfaceArity?: number): void {
  if (interfaceArity !== undefined && (!Number.isSafeInteger(interfaceArity) || interfaceArity < 0)) {
    throw new Error(`interface arity must be a non-negative safe integer, got ${interfaceArity}`)
  }
  const visit = (current: Term, depth: number): void => {
    switch (current.kind) {
      case 'bound':
        if (!Number.isSafeInteger(current.index) || current.index < 0) {
          throw new Error(`bound index must be a non-negative safe integer, got ${current.index}`)
        }
        if (current.index >= depth) {
          throw new Error(`unbound de Bruijn index ${current.index} at depth ${depth}; term is malformed`)
        }
        return
      case 'free':
        if (!Number.isSafeInteger(current.slot) || current.slot < 0) {
          throw new Error(`free slot must be a non-negative safe integer, got ${current.slot}`)
        }
        if (interfaceArity !== undefined && current.slot >= interfaceArity) {
          throw new Error(`free slot ${current.slot} is outside interface arity ${interfaceArity}`)
        }
        return
      case 'lambda':
        visit(current.body, depth + 1)
        return
      case 'application':
        visit(current.fn, depth)
        visit(current.argument, depth)
    }
  }
  visit(term, 0)
}
