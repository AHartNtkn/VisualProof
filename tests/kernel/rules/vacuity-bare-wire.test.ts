import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import type { Diagram } from '../../../src/kernel/diagram/diagram'
import { DiagramError } from '../../../src/kernel/diagram/diagram'
import { derivedScope, polarity } from '../../../src/kernel/diagram/regions'
import { IOTA, relSig, sigEquals, type Sig } from '../../../src/kernel/diagram/sig'
import { RuleError } from '../../../src/kernel/rules/error'
import {
  applyVacuityDelete,
  applyVacuityInsert,
  bareWireAssembly,
  bareWireDescription,
} from '../../../src/kernel/rules/identity-rules'

// Vacuity on one shape — the bare two-point segment, the drawable floating
// existential — swept across both signature sorts and both polarities.
// identity-rules.test.ts states each of the three rules once; this file is
// where the segment's sig-indexing, its gatelessness, and the exact
// insert/delete round trip are pinned.

function wiredWireOf(sig: Sig): { diagram: Diagram; wire: string } {
  const builder = new DiagramBuilder()
  if (sig.kind === 'iota') {
    const ref = builder.ref(builder.root, 'Unary', relSig([IOTA]))
    const wire = builder.wire([{
      node: ref,
      port: { kind: 'arg', index: 0 },
    }], IOTA)
    return { diagram: builder.build(), wire }
  }
  const atom = builder.atom(builder.root, sig)
  const wire = builder.wire([{
    node: atom,
    port: { kind: 'head' },
  }], sig)
  return { diagram: builder.build(), wire }
}

const CASES: readonly (readonly [string, Sig])[] = [
  ['iota', IOTA],
  ['relation sort', relSig([IOTA])],
]

function addedWire(before: Diagram, after: Diagram): string {
  return Object.keys(after.wires).find((wire) => before.wires[wire] === undefined)!
}

describe('bare vacuous wire intro and elim', () => {
  for (const [label, sig] of CASES) {
    describe(label, () => {
      it('introduces a bare wire at positive polarity', () => {
        const diagram = new DiagramBuilder().build()
        expect(polarity(diagram, diagram.root)).toBe('positive')

        const result = applyVacuityInsert(
          diagram,
          bareWireAssembly('bare', diagram.root, sig),
        )
        const added = addedWire(diagram, result)

        expect(derivedScope(result, added)).toBe(diagram.root)
        expect(sigEquals(result.wires[added]!.sig, sig)).toBe(true)
        expect(result.wires[added]!.endpoints).toHaveLength(2)
      })

      it('introduces a bare wire at negative polarity', () => {
        const builder = new DiagramBuilder()
        const cut = builder.cut(builder.root)
        const diagram = builder.build()
        expect(polarity(diagram, cut)).toBe('negative')

        const result = applyVacuityInsert(diagram, bareWireAssembly('bare', cut, sig))
        const added = addedWire(diagram, result)

        expect(derivedScope(result, added)).toBe(cut)
        expect(sigEquals(result.wires[added]!.sig, sig)).toBe(true)
        expect(result.wires[added]!.endpoints).toHaveLength(2)
      })

      it('round-trips by eliminating the bare wire', () => {
        const diagram = new DiagramBuilder().build()
        const introduced = applyVacuityInsert(
          diagram,
          bareWireAssembly('bare', diagram.root, sig),
        )
        const added = addedWire(diagram, introduced)

        expect(applyVacuityDelete(introduced, bareWireDescription(introduced, added)))
          .toEqual(diagram)
      })

      it('refuses every endpoint-bearing wire', () => {
        const { diagram, wire } = wiredWireOf(sig)

        expect(() => bareWireDescription(diagram, wire))
          .toThrowError(/is not bare/)
        expect(() => bareWireDescription(diagram, wire)).toThrow(RuleError)
      })
    })
  }

  it('rejects an unknown scope structurally', () => {
    const diagram = new DiagramBuilder().build()
    expect(() => applyVacuityInsert(diagram, bareWireAssembly('bare', 'ghost', IOTA)))
      .toThrow(DiagramError)
  })

  it('rejects an unknown wire structurally', () => {
    const diagram = new DiagramBuilder().build()
    expect(() => bareWireDescription(diagram, 'ghost'))
      .toThrow(DiagramError)
  })
})
