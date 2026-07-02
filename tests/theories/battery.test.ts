import { describe, it, expect } from 'vitest'
import { buildFregeTheory } from '../../src/theories/frege'
import { buildLambdaTheory } from '../../src/theories/lambda'
import { theoryToJson, loadTheory } from '../../src/kernel/proof/store'
import { applyTheorem } from '../../src/kernel/proof/theorem'
import { termEq } from '../../src/kernel/term/term'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { parseTerm } from '../../src/kernel/term/parse'

const consts = new Set(['ZERO', 'SUCC', 'PLUS', 'ONE', 'TWO'])
const p = (s: string) => parseTerm(s, consts)

describe('bundled theories as shipped artifacts', () => {
  it('both load from their serialized form; onePlusOne applies in a fresh host', () => {
    // frege ships as a relation library (nat) with no theorems
    const frege = loadTheory(JSON.parse(JSON.stringify(theoryToJson(buildFregeTheory()))))
    expect(frege.ctx.relations.has('nat')).toBe(true)
    expect(frege.ctx.theorems.size).toBe(0)

    // lambda ships onePlusOne / fixedPoint; onePlusOne rewrites PLUS ONE ONE -> TWO
    const { ctx } = loadTheory(JSON.parse(JSON.stringify(theoryToJson(buildLambdaTheory()))))
    const onePlusOne = ctx.theorems.get('onePlusOne')!
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('PLUS ONE ONE'))
    const w = h.wire(h.root, [{ node: n, port: { kind: 'output' } }])
    const d = h.build()
    const out = applyTheorem(d, onePlusOne, {
      sel: mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] }),
      args: [w],
    }, 'forward')
    const rewritten = Object.values(out.nodes).some((nd) => nd.kind === 'term' && termEq(nd.term, p('TWO')))
    expect(rewritten).toBe(true)
  })
})
