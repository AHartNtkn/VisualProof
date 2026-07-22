import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import type { Diagram } from '../../../src/kernel/diagram/diagram'
import { DiagramError } from '../../../src/kernel/diagram/diagram'
import { polarity } from '../../../src/kernel/diagram/regions'
import type { Sig } from '../../../src/kernel/diagram/sig'
import { TERM, relSig, sigEquals } from '../../../src/kernel/diagram/sig'
import { RuleError } from '../../../src/kernel/rules/error'
import { applyVacuousIntro, applyVacuousElim } from '../../../src/kernel/rules/vacuous'

const p = (s: string) => parseTerm(s)

/** A diagram with one WIRED (endpoint-carrying) wire of exactly `sig`, plus
 * that wire's id — used to exercise elim's endpoints.length > 0 refusal. */
function wiredWireOf(sig: Sig): { d: Diagram; wireId: string } {
  const h = new DiagramBuilder()
  if (sig.kind === 'term') {
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
  ['TERM', TERM],
  ['relSig([TERM])', relSig([TERM])],
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
    expect(() => applyVacuousIntro(d, 'ghost', TERM)).toThrow(DiagramError)
  })

  it('elim with an unknown wire id throws DiagramError', () => {
    const d = new DiagramBuilder().build()
    expect(() => applyVacuousElim(d, 'ghost')).toThrow(DiagramError)
  })
})
