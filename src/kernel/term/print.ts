import type { Term } from './term'
import { freePorts } from './term'

/**
 * Deterministic printer. Binder at nesting depth d (outermost = 0) is named
 * `x{d}`, prefixed with underscores until it collides with no port name or
 * other binder name in the term. ASCII `\` for lambda.
 */
export function printTerm(t: Term): string {
  const taken = new Set<string>(freePorts(t))
  return go(t, [], taken, 'top')
}

type Ctx = 'top' | 'appFn' | 'appArg'

function go(t: Term, env: string[], taken: Set<string>, ctx: Ctx): string {
  switch (t.kind) {
    case 'bvar': {
      const name = env[env.length - 1 - t.index]
      if (name === undefined) {
        throw new Error(`unbound de Bruijn index ${t.index} at depth ${env.length}; term is malformed`)
      }
      return name
    }
    case 'port': return t.name
    case 'lam': {
      let name = `x${env.length}`
      // env.includes guards a prefix expansion of `x{d}` colliding with an outer
      // binder's chosen name; unreachable under the current scheme (different
      // depths produce different numeric suffixes) but kept as a safety net.
      while (taken.has(name) || env.includes(name)) name = `_${name}`
      const body = go(t.body, [...env, name], taken, 'top')
      const s = `\\${name}. ${body}`
      return ctx === 'top' ? s : `(${s})`
    }
    case 'app': {
      const fn = go(t.fn, env, taken, 'appFn')
      const arg = go(t.arg, env, taken, 'appArg')
      const s = `${fn} ${arg}`
      return ctx === 'appArg' ? `(${s})` : s
    }
  }
}
