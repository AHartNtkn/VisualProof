import type { Term } from './term'
import { lam, app } from './term'
import type { PathSeg } from './reduce'

/** The subterm at a path of body/fn/arg segments. Throws on a path/term mismatch. */
export function subtermAt(t: Term, path: readonly PathSeg[]): Term {
  let cur = t
  for (const [i, seg] of path.entries()) {
    if (seg === 'body' && cur.kind === 'lam') { cur = cur.body; continue }
    if (seg === 'fn' && cur.kind === 'app') { cur = cur.fn; continue }
    if (seg === 'arg' && cur.kind === 'app') { cur = cur.arg; continue }
    throw new Error(`invalid path segment '${seg}' at position ${i} into '${cur.kind}'`)
  }
  return cur
}

/** Replace the subterm at a path. No shifting: callers substitute bvar-closed terms only. */
export function replaceSubtermAt(t: Term, path: readonly PathSeg[], replacement: Term): Term {
  if (path.length === 0) return replacement
  const [seg, ...rest] = path
  if (seg === 'body' && t.kind === 'lam') return lam(replaceSubtermAt(t.body, rest, replacement))
  if (seg === 'fn' && t.kind === 'app') return app(replaceSubtermAt(t.fn, rest, replacement), t.arg)
  if (seg === 'arg' && t.kind === 'app') return app(t.fn, replaceSubtermAt(t.arg, rest, replacement))
  throw new Error(`invalid path segment '${seg}' into '${t.kind}'`)
}

/** True iff every bvar in t is bound by a lam inside t. */
export function isBvarClosed(t: Term): boolean {
  const visit = (u: Term, depth: number): boolean => {
    switch (u.kind) {
      case 'bvar': return u.index < depth
      case 'lam': return visit(u.body, depth + 1)
      case 'app': return visit(u.fn, depth) && visit(u.arg, depth)
      case 'port':
        return true
    }
  }
  return visit(t, 0)
}

/**
 * Replace every occurrence of the named port by s. s must be bvar-closed:
 * a closed term needs no shifting under binders, and ports are a separate
 * namespace from de Bruijn indices, so plain replacement is capture-free.
 */
export function substPort(t: Term, name: string, s: Term): Term {
  if (!isBvarClosed(s)) throw new Error('substPort replacement must be bvar-closed')
  const visit = (u: Term): Term => {
    switch (u.kind) {
      case 'port': return u.name === name ? s : u
      case 'lam': return lam(visit(u.body))
      case 'app': return app(visit(u.fn), visit(u.arg))
      case 'bvar':
        return u
    }
  }
  return visit(t)
}

/** Deterministic fresh port name: the base if free, else base_0, base_1, ... */
export function freshPortName(taken: ReadonlySet<string>, base: string): string {
  if (!taken.has(base)) return base
  for (let i = 0; ; i++) {
    const candidate = `${base}_${i}`
    if (!taken.has(candidate)) return candidate
  }
}
