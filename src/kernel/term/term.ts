export type Term =
  | { readonly kind: 'bvar'; readonly index: number }
  | { readonly kind: 'port'; readonly name: string }
  | { readonly kind: 'const'; readonly id: string }
  | { readonly kind: 'lam'; readonly body: Term }
  | { readonly kind: 'app'; readonly fn: Term; readonly arg: Term }

export function bvar(index: number): Term {
  if (!Number.isSafeInteger(index) || index < 0) {
    throw new Error(`bvar index must be a non-negative safe integer, got ${index} (negative, fractional, or unsafely large indices are meaningless)`)
  }
  return { kind: 'bvar', index }
}

export function port(name: string): Term {
  if (name.length === 0) throw new Error('port name must be non-empty')
  return { kind: 'port', name }
}

export function cnst(id: string): Term {
  if (id.length === 0) throw new Error('const id must be non-empty')
  return { kind: 'const', id }
}

export function lam(body: Term): Term {
  return { kind: 'lam', body }
}

export function app(fn: Term, arg: Term): Term {
  return { kind: 'app', fn, arg }
}

export function termEq(a: Term, b: Term): boolean {
  if (a.kind !== b.kind) return false
  switch (a.kind) {
    case 'bvar': return a.index === (b as Extract<Term, { kind: 'bvar' }>).index
    case 'port': return a.name === (b as Extract<Term, { kind: 'port' }>).name
    case 'const': return a.id === (b as Extract<Term, { kind: 'const' }>).id
    case 'lam': return termEq(a.body, (b as Extract<Term, { kind: 'lam' }>).body)
    case 'app': {
      const bb = b as Extract<Term, { kind: 'app' }>
      return termEq(a.fn, bb.fn) && termEq(a.arg, bb.arg)
    }
  }
}

/** Free ports in first-occurrence order: lam descends into body; app visits fn, then arg. */
export function freePorts(t: Term): string[] {
  const seen = new Set<string>()
  const order: string[] = []
  const visit = (u: Term): void => {
    switch (u.kind) {
      case 'port':
        if (!seen.has(u.name)) { seen.add(u.name); order.push(u.name) }
        return
      case 'lam': visit(u.body); return
      case 'app': visit(u.fn); visit(u.arg); return
      case 'bvar':
      case 'const':
        return
    }
  }
  visit(t)
  return order
}

/**
 * Simultaneous free-port rename: a single traversal in which each port leaf
 * is looked up once by its ORIGINAL name, so chained maps ({a→b, b→a} or
 * {a→b, b→c}) cannot cascade or capture. Leaves not in the map, bound
 * variables, and constants pass through unchanged.
 */
export function renameFreePorts(t: Term, map: ReadonlyMap<string, string>): Term {
  switch (t.kind) {
    case 'port': {
      const to = map.get(t.name)
      return to === undefined ? t : port(to)
    }
    case 'bvar':
    case 'const':
      return t
    case 'lam': return lam(renameFreePorts(t.body, map))
    case 'app': return app(renameFreePorts(t.fn, map), renameFreePorts(t.arg, map))
  }
}

/**
 * Term is a structural type, so object literals can bypass the smart
 * constructors; this re-checks everything they enforce, plus binder scoping:
 * every bvar index must be bound by an enclosing lam. Free variables are
 * ports, never bare bvars.
 */
export function assertWellFormedTerm(t: Term): void {
  const visit = (u: Term, depth: number): void => {
    switch (u.kind) {
      case 'bvar':
        if (!Number.isSafeInteger(u.index) || u.index < 0) {
          throw new Error(`bvar index must be a non-negative safe integer, got ${u.index}`)
        }
        if (u.index >= depth) {
          throw new Error(`unbound de Bruijn index ${u.index} at depth ${depth}; term is malformed`)
        }
        return
      case 'port':
        if (u.name.length === 0) throw new Error('port name must be non-empty')
        return
      case 'const':
        if (u.id.length === 0) throw new Error('const id must be non-empty')
        return
      case 'lam': visit(u.body, depth + 1); return
      case 'app': visit(u.fn, depth); visit(u.arg, depth); return
    }
  }
  visit(t, 0)
}
