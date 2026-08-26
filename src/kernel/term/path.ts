import { application, lambda, type Term } from './term'
import type { PathSeg } from './reduce'

export function subtermAt(term: Term, path: readonly PathSeg[]): Term {
  let current = term
  for (const [position, segment] of path.entries()) {
    if (segment === 'body' && current.kind === 'lambda') {
      current = current.body
      continue
    }
    if (segment === 'fn' && current.kind === 'application') {
      current = current.fn
      continue
    }
    if (segment === 'argument' && current.kind === 'application') {
      current = current.argument
      continue
    }
    throw new Error(`invalid path segment '${segment}' at position ${position} into '${current.kind}'`)
  }
  return current
}

export function replaceSubtermAt(term: Term, path: readonly PathSeg[], replacement: Term): Term {
  if (path.length === 0) return replacement
  const [segment, ...rest] = path
  if (segment === 'body' && term.kind === 'lambda') {
    return lambda(replaceSubtermAt(term.body, rest, replacement))
  }
  if (segment === 'fn' && term.kind === 'application') {
    return application(replaceSubtermAt(term.fn, rest, replacement), term.argument)
  }
  if (segment === 'argument' && term.kind === 'application') {
    return application(term.fn, replaceSubtermAt(term.argument, rest, replacement))
  }
  throw new Error(`invalid path segment '${segment}' into '${term.kind}'`)
}

/** True when every bound index is scoped by a lambda inside the term. */
export function isBoundClosed(term: Term): boolean {
  const visit = (current: Term, depth: number): boolean => {
    switch (current.kind) {
      case 'bound': return current.index < depth
      case 'free': return true
      case 'lambda': return visit(current.body, depth + 1)
      case 'application': return visit(current.fn, depth) && visit(current.argument, depth)
    }
  }
  return visit(term, 0)
}

/** Replace every occurrence of a numeric free slot with a bound-closed term. */
export function substFree(term: Term, slot: number, replacement: Term): Term {
  if (!Number.isSafeInteger(slot) || slot < 0) {
    throw new Error(`free slot must be a non-negative safe integer, got ${slot}`)
  }
  if (!isBoundClosed(replacement)) throw new Error('substFree replacement must be bound-closed')
  const visit = (current: Term): Term => {
    switch (current.kind) {
      case 'bound': return current
      case 'free': return current.slot === slot ? replacement : current
      case 'lambda': return lambda(visit(current.body))
      case 'application': return application(visit(current.fn), visit(current.argument))
    }
  }
  return visit(term)
}
