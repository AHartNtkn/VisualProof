import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import type { Diagram } from '../../../src/kernel/diagram/diagram'
import { DiagramError } from '../../../src/kernel/diagram/diagram'
import { polarity } from '../../../src/kernel/diagram/regions'
import { IOTA, relSig, sigEquals, type Sig } from '../../../src/kernel/diagram/sig'
import { RuleError } from '../../../src/kernel/rules/error'
import {
  applyVacuousElim,
  applyVacuousIntro,
} from '../../../src/kernel/rules/vacuous'

function wiredWireOf(sig: Sig): { diagram: Diagram; wire: string } {
  const builder = new DiagramBuilder()
  if (sig.kind === 'iota') {
    const ref = builder.ref(builder.root, 'Unary', relSig([IOTA]))
    const wire = builder.wire( [{
      node: ref,
      port: { kind: 'arg', index: 0 },
    }], IOTA)
    return { diagram: builder.build(), wire }
  }
  const atom = builder.atom(builder.root, sig)
  const wire = builder.wire( [{
    node: atom,
    port: { kind: 'head' },
  }], sig)
  return { diagram: builder.build(), wire }
}

const CASES: readonly (readonly [string, Sig])[] = [
  ['iota', IOTA],
  ['relation sort', relSig([IOTA])],
]

describe('bare vacuous wire intro and elim', () => {
  for (const [label, sig] of CASES) {
    describe(label, () => {
      it('introduces an endpoint-free wire at positive polarity', () => {
        const diagram = new DiagramBuilder().build()
        expect(polarity(diagram, diagram.root)).toBe('positive')

        const result = applyVacuousIntro(diagram, diagram.root, sig)
        const added = Object.keys(result.wires).find((wire) =>
          diagram.wires[wire] === undefined)!

        expect(result.wires[added]!.scope).toBe(diagram.root)
        expect(sigEquals(result.wires[added]!.sig, sig)).toBe(true)
        expect(result.wires[added]!.endpoints).toEqual([])
      })

      it('introduces an endpoint-free wire at negative polarity', () => {
        const builder = new DiagramBuilder()
        const cut = builder.cut(builder.root)
        const diagram = builder.build()
        expect(polarity(diagram, cut)).toBe('negative')

        const result = applyVacuousIntro(diagram, cut, sig)
        const added = Object.keys(result.wires).find((wire) =>
          diagram.wires[wire] === undefined)!

        expect(result.wires[added]!.scope).toBe(cut)
        expect(sigEquals(result.wires[added]!.sig, sig)).toBe(true)
        expect(result.wires[added]!.endpoints).toEqual([])
      })

      it('round-trips by eliminating the bare wire', () => {
        const diagram = new DiagramBuilder().build()
        const introduced = applyVacuousIntro(
          diagram,
          diagram.root,
          sig,
        )
        const added = Object.keys(introduced.wires).find((wire) =>
          diagram.wires[wire] === undefined)!

        expect(applyVacuousElim(introduced, added)).toEqual(diagram)
      })

      it('refuses every endpoint-bearing wire', () => {
        const { diagram, wire } = wiredWireOf(sig)

        expect(() => applyVacuousElim(diagram, wire))
          .toThrowError(/has 1 endpoint\(s\)/)
        expect(() => applyVacuousElim(diagram, wire)).toThrow(RuleError)
      })
    })
  }

  it('rejects an unknown scope structurally', () => {
    const diagram = new DiagramBuilder().build()
    expect(() => applyVacuousIntro(diagram, 'ghost', IOTA))
      .toThrow(DiagramError)
  })

  it('rejects an unknown wire structurally', () => {
    const diagram = new DiagramBuilder().build()
    expect(() => applyVacuousElim(diagram, 'ghost'))
      .toThrow(DiagramError)
  })
})
