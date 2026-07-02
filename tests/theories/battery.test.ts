import { describe, it, expect } from 'vitest'
import { buildFregeTheory } from '../../src/theories/frege'
import { buildLambdaTheory } from '../../src/theories/lambda'
import { theoryToJson, loadTheory } from '../../src/kernel/proof/store'
import { applyTheorem } from '../../src/kernel/proof/theorem'
import { termEq } from '../../src/kernel/term/term'
import { serializeTerm, deserializeTerm } from '../../src/kernel/term/serialize'
import type { Diagram } from '../../src/kernel/diagram/diagram'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { parseTerm } from '../../src/kernel/term/parse'

const p = (s: string) => parseTerm(s)
const POO = p('(\\m. \\n. \\f. \\x. m f (n f x)) (\\f. \\x. f x) (\\f. \\x. f x)') // pure PLUS ONE ONE
const TWOc = p('\\f. \\x. f (f x)')

/**
 * Every term node round-trips through the pure serializer/deserializer. The
 * pure codec knows only bvar/port/lam/app tags (#, P, L, A); a reintroduced
 * constant would serialize to a C-tag the deserializer rejects, so a clean
 * round-trip is the purge guard.
 */
function assertPureTerms(d: Diagram, where: string): void {
  for (const [id, n] of Object.entries(d.nodes)) {
    if (n.kind !== 'term') continue
    const s = serializeTerm(n.term)
    expect(serializeTerm(deserializeTerm(s)), `${where} node '${id}' is not a pure term`).toBe(s)
  }
}

describe('bundled theories as shipped artifacts', () => {
  it('both load from their serialized form; onePlusOne applies in a fresh host', () => {
    // frege ships the four relations plus the five theorems
    const frege = loadTheory(JSON.parse(JSON.stringify(theoryToJson(buildFregeTheory()))))
    expect([...frege.ctx.relations.keys()].sort()).toEqual(['nat', 'plus', 'succ', 'zero'])
    expect([...frege.ctx.theorems.keys()].sort()).toEqual(['plusAssoc', 'plusComm', 'plusLeftUnit', 'plusRightUnit', 'succShiftS', 'zeroIsNat'])

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

  // The road the app actually uses to bring a theory in is theoryToJson (save)
  // → loadTheory (open), and loadTheory's verifyTheory re-runs checkTheorem on
  // EVERY theorem — a full re-derivation, not a parse. These pins assert both
  // theories survive that road with every theorem intact, and (negative
  // control) that the road genuinely re-verifies: corrupting one theorem's
  // recorded steps makes loadTheory throw rather than silently accept it.
  for (const [label, build] of [['frege', buildFregeTheory], ['lambda', buildLambdaTheory]] as const) {
    it(`${label}: every theorem replays and verifies through theoryToJson → loadTheory`, () => {
      const src = build()
      const { theory } = loadTheory(JSON.parse(JSON.stringify(theoryToJson(src))))
      expect(theory.theorems.map((t) => t.name)).toEqual(src.theorems.map((t) => t.name))
      for (const s of src.theorems) {
        const loaded = theory.theorems.find((t) => t.name === s.name)
        expect(loaded, `theorem '${s.name}' lost in the JSON round-trip`).toBeDefined()
        expect(loaded!.steps.length, `theorem '${s.name}' step count changed`).toBe(s.steps.length)
      }
    })

    it(`${label}: dropping a recorded proof step makes loadTheory reject the theory`, () => {
      const json = theoryToJson(build()) as { theorems: { name: string; steps: unknown[] }[] }
      // corrupt the LAST theorem (the richest derivation of each theory) by
      // dropping its final step: the recorded proof no longer reaches the rhs.
      const victim = json.theorems[json.theorems.length - 1]!
      const broken = JSON.parse(JSON.stringify(json)) as typeof json
      broken.theorems[broken.theorems.length - 1]!.steps.pop()
      expect(victim.steps.length).toBeGreaterThan(0)
      expect(() => loadTheory(broken)).toThrow()
    })
  }

  it('every statement and relation body is a pure term (guards the constant purge)', () => {
    for (const theory of [buildFregeTheory(), buildLambdaTheory()]) {
      for (const [name, rel] of Object.entries(theory.relations)) {
        assertPureTerms(rel.diagram, `relation '${name}'`)
      }
      for (const thm of theory.theorems) {
        assertPureTerms(thm.lhs.diagram, `theorem '${thm.name}' lhs`)
        assertPureTerms(thm.rhs.diagram, `theorem '${thm.name}' rhs`)
      }
    }
  })
})
