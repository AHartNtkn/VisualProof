import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { wireAt } from '../../../src/kernel/rules/access'
import { applyLambdaCongruenceJoin } from '../../../src/kernel/rules/lambda/congruence'
import { application, free } from '../../../src/kernel/term/term'

describe('Lambda congruence join', () => {
  it('joins convertible outputs when corresponding free slots share host wires', () => {
    const builder = new DiagramBuilder()
    const left = builder.term(builder.root, application(free(0), free(1)))
    const right = builder.term(builder.root, application(free(0), free(1)))
    builder.wire([
      { node: left, port: { kind: 'free', index: 0 } },
      { node: right, port: { kind: 'free', index: 0 } },
    ])
    builder.wire([
      { node: left, port: { kind: 'free', index: 1 } },
      { node: right, port: { kind: 'free', index: 1 } },
    ])
    const source = builder.build()
    const leftOutput = wireAt(source, left, { kind: 'output' })

    const result = applyLambdaCongruenceJoin(
      source,
      left,
      right,
      { leftSteps: [], rightSteps: [] },
      { commonArity: 2, left: [0, 1], right: [0, 1] },
    )

    expect(wireAt(result, left, { kind: 'output' })).toBe(leftOutput)
    expect(wireAt(result, right, { kind: 'output' })).toBe(leftOutput)
  })

  it('quotients repeated native slots carried by one physical wire', () => {
    const builder = new DiagramBuilder()
    const left = builder.term(builder.root, application(free(0), free(1)), 2)
    const right = builder.term(builder.root, application(free(0), free(0)), 1)
    builder.wire([
      { node: left, port: { kind: 'free', index: 0 } },
      { node: left, port: { kind: 'free', index: 1 } },
      { node: right, port: { kind: 'free', index: 0 } },
    ])
    const source = builder.build()
    const leftOutput = wireAt(source, left, { kind: 'output' })

    const result = applyLambdaCongruenceJoin(
      source,
      left,
      right,
      { leftSteps: [], rightSteps: [] },
      { commonArity: 1, left: [0, 0], right: [0] },
    )

    expect(wireAt(result, right, { kind: 'output' })).toBe(leftOutput)
  })

  it('rejects a shared correspondence column carried by different wires', () => {
    const builder = new DiagramBuilder()
    const left = builder.term(builder.root, free(0))
    const right = builder.term(builder.root, free(0))
    const source = builder.build()
    expect(() => applyLambdaCongruenceJoin(
      source,
      left,
      right,
      { leftSteps: [], rightSteps: [] },
      { commonArity: 1, left: [0], right: [0] },
    )).toThrow(/common column 0/i)
  })
})
