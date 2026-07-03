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
  it('both load from their serialized form; closed onePlusOne inserts, fixedPoint rewrites in a fresh host', () => {
    // frege ships the four relations plus the eight theorems
    const frege = loadTheory(JSON.parse(JSON.stringify(theoryToJson(buildFregeTheory()))))
    expect([...frege.ctx.relations.keys()].sort()).toEqual(['nat', 'plus', 'succ', 'zero'])
    expect([...frege.ctx.theorems.keys()].sort()).toEqual(['oneIsNat', 'plusAssoc', 'plusComm', 'plusLeftUnit', 'plusRightUnit', 'succNat', 'succShiftS', 'zeroIsNat'])

    const { ctx } = loadTheory(JSON.parse(JSON.stringify(theoryToJson(buildLambdaTheory()))))

    // onePlusOne is the CLOSED equation 1+1=2 (boundary []): cited by inserting
    // the proven sentence into an empty positive host — the inserted line
    // carries BOTH closed descriptions (the join is the content).
    const onePlusOne = ctx.theorems.get('onePlusOne')!
    expect(onePlusOne.lhs.boundary).toHaveLength(0)
    const empty = new DiagramBuilder().build()
    const inserted = applyTheorem(empty, onePlusOne, {
      sel: mkSelection(empty, { region: empty.root, regions: [], nodes: [], wires: [] }),
      args: [],
    }, 'forward')
    const termNodes = Object.values(inserted.nodes).filter((nd) => nd.kind === 'term')
    expect(termNodes).toHaveLength(2)
    const wires = Object.values(inserted.wires)
    expect(wires).toHaveLength(1) // one shared line: the equation
    expect(wires[0]!.endpoints).toHaveLength(2)

    // fixedPoint stays rule-shaped (free f): rewrites `Y f` -> `f (Y f)` in place
    const fixedPoint = ctx.theorems.get('fixedPoint')!
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('(\\g. (\\x. g (x x)) (\\x. g (x x))) f'))
    const wo = h.wire(h.root, [{ node: n, port: { kind: 'output' } }])
    const wf = h.wire(h.root, [{ node: n, port: { kind: 'freeVar', name: 'f' } }])
    const d = h.build()
    const out = applyTheorem(d, fixedPoint, {
      sel: mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] }),
      args: [wo, wf],
    }, 'forward')
    const rewritten = Object.values(out.nodes).some((nd) =>
      nd.kind === 'term' && termEq(nd.term, p('s0 ((\\g. (\\x. g (x x)) (\\x. g (x x))) s0)')))
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
