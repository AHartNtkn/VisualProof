import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { wireAt } from '../../../src/kernel/rules/access'
import { applyLambdaConversion } from '../../../src/kernel/rules/lambda/conversion'
import { application, bound, free, lambda, termEq } from '../../../src/kernel/term/term'
import type { ConversionCertificate } from '../../../src/kernel/term/certificate'

const betaIdentity: ConversionCertificate = {
  leftSteps: [{ kind: 'beta', path: [] }],
  rightSteps: [],
}

describe('applyLambdaConversion', () => {
  it('replays a conversion certificate and preserves output and shared free-slot incidences', () => {
    const builder = new DiagramBuilder()
    const node = builder.term(
      builder.root,
      application(lambda(bound(0)), free(0)),
    )
    const source = builder.build()
    const output = wireAt(source, node, { kind: 'output' })
    const shared = wireAt(source, node, { kind: 'free', index: 0 })

    const converted = applyLambdaConversion(
      source,
      node,
      free(0),
      { commonArity: 1, left: [0], right: [0] },
      betaIdentity,
    )

    const convertedNode = converted.nodes[node]
    expect(convertedNode?.kind).toBe('term')
    if (convertedNode?.kind !== 'term') throw new Error('expected a term node')
    expect(termEq(convertedNode.term, free(0))).toBe(true)
    expect(wireAt(converted, node, { kind: 'output' })).toBe(output)
    expect(wireAt(converted, node, { kind: 'free', index: 0 })).toBe(shared)
  })

  it('attaches a right-only interface slot while transporting a shared slot to its selected column', () => {
    const builder = new DiagramBuilder()
    const node = builder.term(
      builder.root,
      application(lambda(bound(0)), free(0)),
    )
    const attachment = builder.wire([
      { node: builder.identity(builder.root, { kind: 'iota' }, 1), port: { kind: 'identity', index: 0 } },
      { node: builder.identity(builder.root, { kind: 'iota' }, 1), port: { kind: 'identity', index: 0 } },
    ])
    const source = builder.build()
    const shared = wireAt(source, node, { kind: 'free', index: 0 })

    const converted = applyLambdaConversion(
      source,
      node,
      free(1),
      { commonArity: 2, left: [1], right: [0, 1] },
      betaIdentity,
      { 0: attachment },
    )

    expect(wireAt(converted, node, { kind: 'free', index: 0 })).toBe(attachment)
    expect(wireAt(converted, node, { kind: 'free', index: 1 })).toBe(shared)
  })

  it('rejects a forged conversion certificate', () => {
    const builder = new DiagramBuilder()
    const node = builder.term(
      builder.root,
      application(lambda(bound(0)), free(0)),
    )
    const source = builder.build()

    expect(() => applyLambdaConversion(
      source,
      node,
      free(0),
      { commonArity: 1, left: [0], right: [0] },
      { leftSteps: [], rightSteps: [] },
    )).toThrowError(/conversion certificate rejected/i)
  })
})
