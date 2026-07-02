import { parseTerm } from '../kernel/term/parse'
import { DiagramBuilder } from '../kernel/diagram/builder'
import { mkDiagramWithBoundary, type DiagramWithBoundary } from '../kernel/diagram/boundary'
import type { Definitions } from '../kernel/rules/definitions'
import type { Theory } from '../kernel/proof/store'

const consts = new Set(['ZERO', 'SUCC', 'PLUS', 'ONE', 'TWO'])
const p = (s: string) => parseTerm(s, consts)
const noConsts = new Set<string>()
const pp = (s: string) => parseTerm(s, noConsts)

export const fregeDefinitions: Definitions = {
  ZERO: pp('\\f. \\x. x'),
  ONE: pp('\\f. \\x. f x'),
  TWO: pp('\\f. \\x. f (f x)'),
  SUCC: pp('\\n. \\f. \\x. f (n f x)'),
  PLUS: pp('\\m. \\n. \\f. \\x. m f (n f x)'),
}

/**
 * The general ℕ(x) — inCutNat. The base line w0 is scoped at the guard bubble
 * rB (NOT the root): the zero-witness lives strictly inside the cut, so ℕ is
 * non-vacuous (∃w0 is not witnessable outside the guard by a non-zero). The
 * boundary is the x-line, the only wire that leaves the cut.
 */
export function natRelation(): DiagramWithBoundary {
  const l = new DiagramBuilder()
  const cut1 = l.cut(l.root)
  const rB = l.bubble(cut1, 1)
  const nz = l.termNode(rB, p('ZERO'))
  const a0 = l.atom(rB, rB)
  // the base zero-line is scoped INSIDE the guard bubble (the non-vacuity fix)
  l.wire(rB, [
    { node: nz, port: { kind: 'output' } },
    { node: a0, port: { kind: 'arg', index: 0 } },
  ])
  const cut2 = l.cut(rB)
  const a1 = l.atom(cut2, rB)
  const ny = l.termNode(cut2, p('SUCC y'))
  l.wire(cut2, [
    { node: a1, port: { kind: 'arg', index: 0 } },
    { node: ny, port: { kind: 'freeVar', name: 'y' } },
  ])
  const cut3 = l.cut(cut2)
  const a2 = l.atom(cut3, rB)
  l.wire(cut2, [
    { node: ny, port: { kind: 'output' } },
    { node: a2, port: { kind: 'arg', index: 0 } },
  ])
  const cut4 = l.cut(rB)
  const a3 = l.atom(cut4, rB)
  const wx = l.wire(l.root, [{ node: a3, port: { kind: 'arg', index: 0 } }])
  return mkDiagramWithBoundary(l.build(), [wx])
}

export function buildFregeTheory(): Theory {
  return {
    definitions: fregeDefinitions,
    relations: { nat: natRelation() },
    theorems: [],
  }
}
