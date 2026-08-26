import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { joinWires } from '../../../src/app/edit'
import { wireAt } from '../../../src/kernel/rules/access'
import {
  applyLambdaFission,
  applyLambdaFusion,
} from '../../../src/kernel/rules/lambda/fission'
import { application, bound, free, lambda, termEq } from '../../../src/kernel/term/term'

describe('Lambda fission and fusion', () => {
  it('extracts the selected whole subterm and fuses back to the starting graph', () => {
    const builder = new DiagramBuilder()
    const selected = application(lambda(bound(0)), free(1))
    const node = builder.term(builder.root, application(free(0), selected), 2)
    const source = builder.build()

    const split = applyLambdaFission(source, node, ['argument'])
    const producer = Object.keys(split.nodes).find((id) => source.nodes[id] === undefined)!
    const bridge = Object.keys(split.wires).find((id) => source.wires[id] === undefined)!
    const made = split.nodes[producer]
    expect(made?.kind).toBe('term')
    if (made?.kind !== 'term') throw new Error('expected extracted term producer')
    expect(termEq(made.term, application(lambda(bound(0)), free(1)))).toBe(true)
    expect(made.freeArity).toBe(2)
    expect(wireAt(split, producer, { kind: 'free', index: 1 }))
      .toBe(wireAt(source, node, { kind: 'free', index: 1 }))

    expect(applyLambdaFusion(split, bridge)).toEqual(source)
  })

  it('preserves distinct native slots that share one host wire across round trip', () => {
    const builder = new DiagramBuilder()
    const node = builder.term(
      builder.root,
      application(free(0), application(free(0), free(1))),
      2,
    )
    const initial = builder.build()
    const source = joinWires(initial, [
      wireAt(initial, node, { kind: 'free', index: 0 }),
      wireAt(initial, node, { kind: 'free', index: 1 }),
    ])

    const split = applyLambdaFission(source, node, ['argument'])
    const bridge = Object.keys(split.wires)
      .find((wire) => source.wires[wire] === undefined)!

    expect(applyLambdaFusion(split, bridge)).toEqual(source)
  })

  it('rejects a subterm that references a binder above the selected path', () => {
    const builder = new DiagramBuilder()
    const node = builder.term(builder.root, lambda(application(bound(0), free(0))))
    const source = builder.build()
    expect(() => applyLambdaFission(source, node, ['body', 'fn']))
      .toThrow(/references binders above/i)
  })
})
