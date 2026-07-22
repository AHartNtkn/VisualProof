import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { EMPTY_PROOF_CONTEXT, extendRelations } from '../../src/kernel/proof/context'
import { parseTerm } from '../../src/kernel/term/parse'
import { buildFregeTheory } from '../../src/theories/frege'
import { verifyTheory } from '../../src/kernel/proof/store'
import { resolveNamedRelationInstantiation } from '../../src/interaction/named-relation'

const context = () => verifyTheory(buildFregeTheory())

function negativeBubble(arity: number): { readonly diagram: ReturnType<DiagramBuilder['build']>; readonly bubble: string } {
  const builder = new DiagramBuilder()
  const cut = builder.cut(builder.root)
  const bubble = builder.bubble(cut, arity)
  const atom = builder.atom(bubble, bubble)
  for (let index = 0; index < arity; index++) {
    builder.wire(bubble, [{ node: atom, port: { kind: 'arg', index } }])
  }
  return { diagram: builder.build(), bubble }
}

function relationWithArity(arity: number) {
  const builder = new DiagramBuilder()
  const node = builder.termNode(builder.root, parseTerm('\\f. f x0 x1 x2'),
    Array.from({ length: arity }, (_, index) => `x${index}`))
  const boundary = Array.from({ length: arity }, (_, index) =>
    builder.wire(builder.root, [{ node, port: { kind: 'freeVar' as const, name: `x${index}` } }]))
  return mkDiagramWithBoundary(builder.build(), boundary)
}

describe('named relation instantiation resolver', () => {
  it('returns a closed folded step for an exact-arity named relation', () => {
    const target = negativeBubble(2)

    expect(resolveNamedRelationInstantiation(target.diagram, target.bubble, context(), 'succ', 'forward'))
      .toMatchObject({
        rule: 'comprehensionInstantiate',
        bubble: target.bubble,
        attachments: [],
        binders: [],
        comp: {
          boundary: expect.any(Array),
          diagram: { nodes: expect.any(Object) },
        },
      })
  })

  it('refuses an unknown named relation before constructing a step', () => {
    const target = negativeBubble(0)

    expect(() => resolveNamedRelationInstantiation(target.diagram, target.bubble, context(), 'missing', 'forward'))
      .toThrow(/unknown named relation 'missing'/)
  })

  it('refuses a named relation with extra boundary parameters instead of inferring attachments', () => {
    const target = negativeBubble(2)
    const proof = extendRelations(EMPTY_PROOF_CONTEXT, [['three', relationWithArity(3)]])

    expect(() => resolveNamedRelationInstantiation(target.diagram, target.bubble, proof, 'three', 'forward'))
      .toThrow(/arity mismatch.*three.*3.*2/i)
  })

  it('refuses a non-bubble target', () => {
    const builder = new DiagramBuilder()

    expect(() => resolveNamedRelationInstantiation(builder.build(), builder.root, context(), 'succ', 'forward'))
      .toThrow(/requires a bubble target/i)
  })

  it('refuses when the kernel rejects the target orientation', () => {
    const builder = new DiagramBuilder()
    const bubble = builder.bubble(builder.root, 2)
    const atom = builder.atom(bubble, bubble)
    for (let index = 0; index < 2; index++) {
      builder.wire(bubble, [{ node: atom, port: { kind: 'arg', index } }])
    }

    expect(() => resolveNamedRelationInstantiation(builder.build(), bubble, context(), 'succ', 'forward'))
      .toThrow(/requires a negative bubble/i)
  })
})
