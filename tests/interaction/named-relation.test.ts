import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { relSig, TERM } from '../../src/kernel/diagram/sig'
import { EMPTY_PROOF_CONTEXT, extendRelations } from '../../src/kernel/proof/context'
import { parseTerm } from '../../src/kernel/term/parse'
import { buildFregeTheory } from '../../src/theories/frege'
import { verifyTheory } from '../../src/kernel/proof/store'
import { resolveNamedRelationInstantiation } from '../../src/interaction/named-relation'

const context = () => verifyTheory(buildFregeTheory())
const R = (n: number) => relSig(Array.from({ length: n }, () => TERM))

/** A relational wire of the given arity at a NEGATIVE scope (a cut), carrying one
 *  atom occurrence by its head — the wire-model image of a bound-predicate bubble. */
function negativeWire(arity: number): { readonly diagram: ReturnType<DiagramBuilder['build']>; readonly wire: string } {
  const builder = new DiagramBuilder()
  const cut = builder.cut(builder.root)
  const atom = builder.atom(cut, R(arity))
  const wire = builder.wire(cut, [{ node: atom, port: { kind: 'head' } }], R(arity))
  for (let index = 0; index < arity; index++) {
    builder.wire(cut, [{ node: atom, port: { kind: 'arg', index } }])
  }
  return { diagram: builder.build(), wire }
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
  it('returns a closed body-attach step for an exact-arity named relation', () => {
    const target = negativeWire(2)

    expect(resolveNamedRelationInstantiation(target.diagram, target.wire, context(), 'succ', 'forward'))
      .toMatchObject({
        rule: 'bodyAttach',
        wireId: target.wire,
        params: [],
        content: {
          boundary: expect.any(Array),
          diagram: { nodes: expect.any(Object) },
        },
      })
  })

  it('refuses an unknown named relation before constructing a step', () => {
    const target = negativeWire(1)

    expect(() => resolveNamedRelationInstantiation(target.diagram, target.wire, context(), 'missing', 'forward'))
      .toThrow(/unknown named relation 'missing'/)
  })

  it('refuses a named relation with extra boundary parameters instead of inferring attachments', () => {
    const target = negativeWire(2)
    const proof = extendRelations(EMPTY_PROOF_CONTEXT, [['three', relationWithArity(3)]])

    expect(() => resolveNamedRelationInstantiation(target.diagram, target.wire, proof, 'three', 'forward'))
      .toThrow(/arity mismatch.*three.*3.*2/i)
  })

  it('refuses a non-relational target wire', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const w = builder.wire(cut, [])
    expect(() => resolveNamedRelationInstantiation(builder.build(), w, context(), 'succ', 'forward'))
      .toThrow(/requires a relational wire/i)
  })

  it('refuses when the kernel rejects the target orientation', () => {
    // a relational wire at a POSITIVE scope (root): forward body-attach refuses.
    const builder = new DiagramBuilder()
    const atom = builder.atom(builder.root, R(2))
    const wire = builder.wire(builder.root, [{ node: atom, port: { kind: 'head' } }], R(2))
    for (let index = 0; index < 2; index++) {
      builder.wire(builder.root, [{ node: atom, port: { kind: 'arg', index } }])
    }

    expect(() => resolveNamedRelationInstantiation(builder.build(), wire, context(), 'succ', 'forward'))
      .toThrow(/requires a negative/i)
  })
})
