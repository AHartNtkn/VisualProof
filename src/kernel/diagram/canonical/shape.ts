import type { Term } from '../../term/term'
import { app, assertWellFormedTerm, cnst, freePorts, lam, port, bvar } from '../../term/term'
import { serializeTerm } from '../../term/serialize'
import type { Port } from '../diagram'
import { DiagramError } from '../diagram'

/**
 * The shape key of a term node: its term with free ports renamed positionally
 * (p0, p1, … in first-occurrence order), serialized. Two term nodes denote the
 * same positional constructor relation iff their shape keys are equal — free
 * variable names are internal labels, not content (spec §2.2).
 */
export function termShapeKey(t: Term): string {
  assertWellFormedTerm(t)
  const order = freePorts(t)
  const rename = new Map(order.map((name, i) => [name, `p${i}`]))
  return serializeTerm(renamePorts(t, rename))
}

function renamePorts(t: Term, rename: ReadonlyMap<string, string>): Term {
  switch (t.kind) {
    case 'port': {
      const next = rename.get(t.name)
      if (next === undefined) {
        throw new DiagramError(`port '${t.name}' missing from rename map; freePorts must cover all ports`)
      }
      return port(next)
    }
    case 'lam': return lam(renamePorts(t.body, rename))
    case 'app': return app(renamePorts(t.fn, rename), renamePorts(t.arg, rename))
    case 'bvar': return bvar(t.index)
    case 'const': return cnst(t.id)
  }
}

/**
 * Positional key for a port: 'out' for the output, 'v{i}' for the free
 * variable at first-occurrence position i, 'a{i}' for atom args. Used by the
 * canonical form so wire endpoints are name-independent.
 */
export function positionalPortKey(termOfNode: Term, p: Port): string {
  switch (p.kind) {
    case 'output': return 'out'
    case 'arg': return `a${p.index}`
    case 'freeVar': {
      const i = freePorts(termOfNode).indexOf(p.name)
      if (i < 0) throw new DiagramError(`'${p.name}' is not a free variable of the term`)
      return `v${i}`
    }
  }
}
