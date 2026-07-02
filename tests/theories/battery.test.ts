import { describe, it, expect } from 'vitest'
import { buildFregeTheory } from '../../src/theories/frege'
import { buildLambdaTheory } from '../../src/theories/lambda'
import { theoryToJson, loadTheory } from '../../src/kernel/proof/store'
import { applyTheorem } from '../../src/kernel/proof/theorem'
import { termEq } from '../../src/kernel/term/term'
import type { Term } from '../../src/kernel/term/term'
import type { Diagram } from '../../src/kernel/diagram/diagram'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { parseTerm } from '../../src/kernel/term/parse'

const p = (s: string) => parseTerm(s, new Set<string>())
const POO = p('(\\m. \\n. \\f. \\x. m f (n f x)) (\\f. \\x. f x) (\\f. \\x. f x)') // pure PLUS ONE ONE
const TWOc = p('\\f. \\x. f (f x)')

/** True if any term node in the diagram carries a `const` constructor. */
function anyConstNode(d: Diagram): boolean {
  const hasConst = (t: Term): boolean => {
    switch (t.kind) {
      case 'const': return true
      case 'lam': return hasConst(t.body)
      case 'app': return hasConst(t.fn) || hasConst(t.arg)
      default: return false
    }
  }
  return Object.values(d.nodes).some((n) => n.kind === 'term' && hasConst(n.term))
}

describe('bundled theories as shipped artifacts', () => {
  it('both load from their serialized form; onePlusOne applies in a fresh host', () => {
    // frege ships the four relations plus the five theorems
    const frege = loadTheory(JSON.parse(JSON.stringify(theoryToJson(buildFregeTheory()))))
    expect([...frege.ctx.relations.keys()].sort()).toEqual(['nat', 'plus', 'succ', 'zero'])
    expect([...frege.ctx.theorems.keys()].sort()).toEqual(['plusAssoc', 'plusComm', 'plusLeftUnit', 'plusRightUnit', 'succShiftS'])

    // lambda ships onePlusOne / fixedPoint; onePlusOne rewrites (PLUS ONE ONE) -> TWO
    const { ctx } = loadTheory(JSON.parse(JSON.stringify(theoryToJson(buildLambdaTheory()))))
    const onePlusOne = ctx.theorems.get('onePlusOne')!
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, POO)
    const w = h.wire(h.root, [{ node: n, port: { kind: 'output' } }])
    const d = h.build()
    const out = applyTheorem(d, onePlusOne, {
      sel: mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] }),
      args: [w],
    }, 'forward')
    const rewritten = Object.values(out.nodes).some((nd) => nd.kind === 'term' && termEq(nd.term, TWOc))
    expect(rewritten).toBe(true)
  })

  it('no statement or relation body contains a term constant (guards the constant purge)', () => {
    for (const theory of [buildFregeTheory(), buildLambdaTheory()]) {
      for (const [name, rel] of Object.entries(theory.relations)) {
        expect(anyConstNode(rel.diagram), `relation '${name}' has a const node`).toBe(false)
      }
      for (const thm of theory.theorems) {
        expect(anyConstNode(thm.lhs.diagram), `theorem '${thm.name}' lhs has a const node`).toBe(false)
        expect(anyConstNode(thm.rhs.diagram), `theorem '${thm.name}' rhs has a const node`).toBe(false)
      }
    }
  })
})
