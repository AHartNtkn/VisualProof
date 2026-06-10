export type Term =
  | { readonly kind: 'bvar'; readonly index: number }
  | { readonly kind: 'port'; readonly name: string }
  | { readonly kind: 'const'; readonly id: string }
  | { readonly kind: 'lam'; readonly body: Term }
  | { readonly kind: 'app'; readonly fn: Term; readonly arg: Term }

export function bvar(index: number): Term {
  if (index < 0 || !Number.isInteger(index)) {
    throw new Error(`bvar index must be a non-negative integer, got ${index} (negative or fractional indices are meaningless)`)
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
    case 'bvar': return a.index === (b as typeof a).index
    case 'port': return a.name === (b as typeof a).name
    case 'const': return a.id === (b as typeof a).id
    case 'lam': return termEq(a.body, (b as typeof a).body)
    case 'app': {
      const bb = b as typeof a
      return termEq(a.fn, bb.fn) && termEq(a.arg, bb.arg)
    }
  }
}

/** Free ports in first-occurrence order: lam descends into body; app visits fn, then arg. */
export function freePorts(t: Term): string[] {
  const seen: string[] = []
  const visit = (u: Term): void => {
    switch (u.kind) {
      case 'port':
        if (!seen.includes(u.name)) seen.push(u.name)
        return
      case 'lam': visit(u.body); return
      case 'app': visit(u.fn); visit(u.arg); return
      case 'bvar':
      case 'const':
        return
    }
  }
  visit(t)
  return seen
}
