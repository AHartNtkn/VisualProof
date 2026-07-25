import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import type { Diagram, DiagramNode, Wire } from '../../../src/kernel/diagram/diagram'
import { DiagramError, mkDiagram } from '../../../src/kernel/diagram/diagram'
import { mkDiagramWithBoundary, type DiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { polarity } from '../../../src/kernel/diagram/regions'
import type { Sig } from '../../../src/kernel/diagram/sig'
import { IOTA, relSig, sigEquals } from '../../../src/kernel/diagram/sig'
import { exploreForm } from '../../../src/kernel/diagram/canonical/explore'
import { RuleError } from '../../../src/kernel/rules/error'
import { applyBodyAttach } from '../../../src/kernel/rules/body'
import { applyVacuousIntro, applyVacuousElim } from '../../../src/kernel/rules/vacuous'

const p = (s: string) => parseTerm(s)
const R1 = relSig([IOTA])

/** Content interface: arg stubs then param stubs, root-scoped endpoint-free. */
function mkContent(argSigs: readonly Sig[], paramSigs: readonly Sig[]): DiagramWithBoundary {
  const wires: Record<string, Wire> = {}
  const boundary: string[] = []
  argSigs.forEach((s, i) => { wires[`aw${i}`] = { scope: 'c0', sig: s, endpoints: [] }; boundary.push(`aw${i}`) })
  paramSigs.forEach((s, j) => { wires[`pw${j}`] = { scope: 'c0', sig: s, endpoints: [] }; boundary.push(`pw${j}`) })
  return mkDiagramWithBoundary(
    mkDiagram({ root: 'c0', regions: { c0: { kind: 'sheet' } }, wires }),
    boundary,
  )
}

const bodyNodesOf = (d: Diagram): [string, Extract<DiagramNode, { kind: 'body' }>][] =>
  Object.entries(d.nodes).filter((e): e is [string, Extract<DiagramNode, { kind: 'body' }>] => e[1].kind === 'body')

/** A diagram with one WIRED (endpoint-carrying) wire of exactly `sig`, plus
 * that wire's id — used to exercise elim's endpoints.length > 0 refusal. */
function wiredWireOf(sig: Sig): { d: Diagram; wireId: string } {
  const h = new DiagramBuilder()
  if (sig.kind === 'iota') {
    const n = h.termNode(h.root, p('\\x. x'))
    const d = h.build()
    const wireId = Object.entries(d.wires).find(([, w]) =>
      w.endpoints.some((e) => e.node === n && e.port.kind === 'output'))![0]
    return { d, wireId }
  }
  const n = h.atom(h.root, sig)
  const d = h.build()
  const wireId = Object.entries(d.wires).find(([, w]) =>
    w.endpoints.some((e) => e.node === n && e.port.kind === 'head'))![0]
  return { d, wireId }
}

const CASES: readonly (readonly [string, Sig])[] = [
  ['IOTA', IOTA],
  ['relSig([IOTA])', relSig([IOTA])],
]

describe('vacuous wire intro/elim', () => {
  for (const [label, sig] of CASES) {
    describe(`sig = ${label}`, () => {
      it('intro at a POSITIVE scope adds a fresh endpoint-free wire of sig', () => {
        const h = new DiagramBuilder()
        const d = h.build()
        expect(polarity(d, d.root)).toBe('positive')
        const out = applyVacuousIntro(d, d.root, sig)
        const addedId = Object.keys(out.wires).find((id) => d.wires[id] === undefined)!
        const added = out.wires[addedId]!
        expect(added.scope).toBe(d.root)
        expect(sigEquals(added.sig, sig)).toBe(true)
        expect(added.endpoints).toHaveLength(0)
      })

      it('intro at a NEGATIVE scope also succeeds (no polarity gate)', () => {
        const h = new DiagramBuilder()
        const cut = h.cut(h.root)
        const d = h.build()
        expect(polarity(d, cut)).toBe('negative')
        const out = applyVacuousIntro(d, cut, sig)
        const addedId = Object.keys(out.wires).find((id) => d.wires[id] === undefined)!
        const added = out.wires[addedId]!
        expect(added.scope).toBe(cut)
        expect(sigEquals(added.sig, sig)).toBe(true)
        expect(added.endpoints).toHaveLength(0)
      })

      it('elim removes an endpoint-free wire, round-tripping with intro', () => {
        const h = new DiagramBuilder()
        const d = h.build()
        const out = applyVacuousIntro(d, d.root, sig)
        const addedId = Object.keys(out.wires).find((id) => d.wires[id] === undefined)!
        const back = applyVacuousElim(out, addedId)
        expect(back).toEqual(d)
      })

      it('elim refuses a wired wire, naming the endpoint count', () => {
        const { d, wireId } = wiredWireOf(sig)
        expect(() => applyVacuousElim(d, wireId))
          .toThrowError(/has 1 endpoint\(s\)/)
        expect(() => applyVacuousElim(d, wireId)).toThrow(RuleError)
      })
    })
  }

  it('intro with an unknown scope throws DiagramError', () => {
    const d = new DiagramBuilder().build()
    expect(() => applyVacuousIntro(d, 'ghost', IOTA)).toThrow(DiagramError)
  })

  it('elim with an unknown wire id throws DiagramError', () => {
    const d = new DiagramBuilder().build()
    expect(() => applyVacuousElim(d, 'ghost')).toThrow(DiagramError)
  })
})

/**
 * Bodied vacuous intro/elim: the comprehension axiom ∃R.R=G ≡ ⊤. Creatable and
 * deletable at ANY polarity, with or without parameters; the solely-bodied
 * shape is the only nonempty wire elim accepts.
 */
describe('bodied vacuous intro/elim (comprehension axiom)', () => {
  for (const [label, scopeOf, wantPolarity] of [
    ['positive root', (h: DiagramBuilder) => h.root, 'positive'],
    ['negative cut', (h: DiagramBuilder) => h.cut(h.root), 'negative'],
  ] as const) {
    it(`bodied intro adds wire + witness body at a ${label}`, () => {
      const h = new DiagramBuilder()
      const scope = scopeOf(h)
      const d = h.build()
      expect(polarity(d, scope)).toBe(wantPolarity)
      const out = applyVacuousIntro(d, scope, R1, undefined, { content: mkContent([IOTA], []), params: [] })
      const wireId = Object.keys(out.wires).find((id) => d.wires[id] === undefined)!
      const bodies = bodyNodesOf(out)
      expect(bodies).toHaveLength(1)
      const [bid, body] = bodies[0]!
      expect(body.region).toBe(scope)
      // the wire's SOLE endpoint is that body's output
      expect(out.wires[wireId]!.endpoints).toEqual([{ node: bid, port: { kind: 'output' } }])
    })

    it(`bodied intro then bodied elim round-trips at a ${label}`, () => {
      const h = new DiagramBuilder()
      const scope = scopeOf(h)
      const d = h.build()
      const out = applyVacuousIntro(d, scope, R1, undefined, { content: mkContent([IOTA], []), params: [] })
      const wireId = Object.keys(out.wires).find((id) => d.wires[id] === undefined)!
      const back = applyVacuousElim(out, wireId)
      expect(exploreForm(back)).toBe(exploreForm(d))
    })
  }

  it('bodied intro with a parameter lands the body freeVar on the param wire; elim trims it back', () => {
    const h = new DiagramBuilder()
    const pW = h.wire(h.root, [], IOTA) // param host line
    const d = h.build()
    const out = applyVacuousIntro(d, d.root, R1, undefined, { content: mkContent([IOTA], [IOTA]), params: [pW] })
    const [bid] = bodyNodesOf(out)[0]!
    // param wire carries the body's p0 freeVar
    expect(out.wires[pW]!.endpoints).toEqual([{ node: bid, port: { kind: 'freeVar', name: 'p0' } }])
    // elim removes wire + body and trims p0 off the param wire
    const wireId = Object.keys(out.wires).find((id) => d.wires[id] === undefined)!
    const back = applyVacuousElim(out, wireId)
    expect(bodyNodesOf(back)).toHaveLength(0)
    expect(back.wires[pW]!.endpoints).toHaveLength(0)
    expect(exploreForm(back)).toBe(exploreForm(d))
  })

  it('bodied intro refuses a IOTA sig (bodies attach only to relational wires)', () => {
    const d = new DiagramBuilder().build()
    expect(() => applyVacuousIntro(d, d.root, IOTA, undefined, { content: mkContent([IOTA], []), params: [] }))
      .toThrowError(/not a relation signature/)
  })

  it('bodied intro refuses a parameter scoped strictly inside the new wire scope', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const inner = h.cut(cut)
    const captured = h.wire(inner, [], IOTA)
    const d = h.build()
    expect(() => applyVacuousIntro(d, cut, R1, undefined, { content: mkContent([IOTA], [IOTA]), params: [captured] }))
      .toThrowError(/at or outside the target wire's scope/)
  })

  it('bodied elim refuses when an atom still rides the wire (not solely bodied)', () => {
    // Mid-instantiate shape: the wire carries a body output AND an atom head.
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const atom = h.atom(cut, R1)
    const W = h.wire(cut, [{ node: atom, port: { kind: 'head' } }], R1)
    h.wire(cut, [{ node: atom, port: { kind: 'arg', index: 0 } }], IOTA)
    const withBody = applyBodyAttach(h.build(), W, mkContent([IOTA], []), [], 'forward')
    expect(withBody.wires[W]!.endpoints).toHaveLength(2)
    expect(() => applyVacuousElim(withBody, W)).toThrowError(/has 2 endpoint\(s\)/)
    expect(() => applyVacuousElim(withBody, W)).toThrow(RuleError)
  })
})
