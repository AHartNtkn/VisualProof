import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { sameDiagram } from '../../../src/kernel/diagram/canonical/iso'
import {
  EMPTY_PROOF_CONTEXT,
  applyTheorem,
  citeLibraryProposition,
  libraryProposition,
  registerTheorem,
  singleStepAction,
  type Theorem,
} from '../../../src/kernel/proof'
import { applyDoubleCutIntro } from '../../../src/kernel/rules/doublecut'

const blank = new DiagramBuilder().build()
const stated = applyDoubleCutIntro(blank, {
  region: blank.root, regions: [], nodes: [], wires: [],
})
const entry = libraryProposition('bare-double-cut', stated)

function bareDoubleCutTheorem(): Theorem {
  return {
    name: 'bare-double-cut',
    lhs: { diagram: blank, boundary: [] },
    rhs: { diagram: stated, boundary: [] },
    actions: [singleStepAction('introduce a bare double cut', {
      rule: 'doubleCutIntro',
      sel: { region: blank.root, regions: [], nodes: [], wires: [] },
    })],
  }
}

describe('trusted library propositions', () => {
  // Catches a proof-theorem polarity gate incorrectly rejecting a trusted citation.
  it.each(['positive', 'negative'] as const)('inserts at %s polarity without proof data', (sign) => {
    const host = new DiagramBuilder()
    const target = sign === 'positive' ? host.root : host.cut(host.root)

    const result = citeLibraryProposition(host.build(), entry, target)

    expect(Object.values(result.regions).filter((region) =>
      region.kind === 'cut' && region.parent === target,
    )).toHaveLength(1)
  })

  // Catches a library entry retaining an open boundary or mutable proof payload.
  it('returns a frozen proposition with no external boundary', () => {
    expect(entry).toMatchObject({ name: 'bare-double-cut', diagram: stated })
    expect(entry).not.toHaveProperty('boundary')
    expect(Object.isFrozen(entry)).toBe(true)
  })

  // Catches accepting an invalid library identifier before it can become authority.
  it('rejects a blank proposition name', () => {
    expect(() => libraryProposition('', stated)).toThrow()
  })

  // Catches library citation drifting from the native theorem occurrence rewrite.
  it.each(['positive', 'negative'] as const)('matches theorem application at %s polarity', (sign) => {
    const host = new DiagramBuilder()
    const target = sign === 'positive' ? host.root : host.cut(host.root)
    const diagram = host.build()
    const theorem = bareDoubleCutTheorem()
    const context = registerTheorem(EMPTY_PROOF_CONTEXT, theorem)

    const cited = citeLibraryProposition(diagram, entry, target)
    const applied = applyTheorem(diagram, context, theorem.name, {
      sel: { region: target, regions: [], nodes: [], wires: [] },
      args: [],
    }, 'forward', sign === 'positive' ? 'forward' : 'backward')

    expect(sameDiagram(cited, applied)).toBe(true)
  })
})
