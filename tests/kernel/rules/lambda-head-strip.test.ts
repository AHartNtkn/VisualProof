import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { wireAt } from '../../../src/kernel/rules/access'
import { applyLambdaHeadStrip } from '../../../src/kernel/rules/lambda/head-strip'
import { application, bound, free, lambda } from '../../../src/kernel/term/term'

describe('Lambda head strip', () => {
  it('replaces an equal rigid head equation with its argument equation', () => {
    const builder = new DiagramBuilder()
    const left = builder.term(builder.root, lambda(application(bound(0), free(0))))
    const right = builder.term(builder.root, lambda(application(bound(0), free(0))))
    const equation = builder.wire([
      { node: left, port: { kind: 'output' } },
      { node: right, port: { kind: 'output' } },
    ])
    const source = builder.build()

    const result = applyLambdaHeadStrip(
      source,
      left,
      right,
      { commonArity: 2, left: [0], right: [1] },
    )

    expect(result.nodes[left]).toBeUndefined()
    expect(result.nodes[right]).toBeUndefined()
    expect(result.wires[equation]).toBeUndefined()
    const termNodes = Object.entries(result.nodes)
      .filter(([, node]) => node.kind === 'term')
    expect(termNodes).toHaveLength(2)
    const replacementEquation = Object.values(result.wires).find((wire) =>
      wire.endpoints.length === 2
      && wire.endpoints.every((endpoint) => endpoint.port.kind === 'output'))
    expect(replacementEquation).toBeDefined()
  })

  it('accepts repeated correspondence columns only when slots share a wire', () => {
    const builder = new DiagramBuilder()
    const left = builder.term(
      builder.root,
      lambda(application(application(bound(0), free(0)), free(1))),
      2,
    )
    const right = builder.term(
      builder.root,
      lambda(application(application(bound(0), free(0)), free(0))),
      1,
    )
    builder.wire([
      { node: left, port: { kind: 'free', index: 0 } },
      { node: left, port: { kind: 'free', index: 1 } },
      { node: right, port: { kind: 'free', index: 0 } },
    ])
    builder.wire([
      { node: left, port: { kind: 'output' } },
      { node: right, port: { kind: 'output' } },
    ])
    const source = builder.build()

    const result = applyLambdaHeadStrip(
      source,
      left,
      right,
      { commonArity: 1, left: [0, 0], right: [0] },
    )

    expect(Object.values(result.nodes).filter((node) => node.kind === 'term'))
      .toEqual([])
  })

  it('rejects a repeated correspondence column carried by different wires', () => {
    const builder = new DiagramBuilder()
    const left = builder.term(
      builder.root,
      lambda(application(application(bound(0), free(0)), free(1))),
      2,
    )
    const right = builder.term(
      builder.root,
      lambda(application(application(bound(0), free(0)), free(0))),
      1,
    )
    builder.wire([
      { node: left, port: { kind: 'free', index: 0 } },
      { node: right, port: { kind: 'free', index: 0 } },
    ])
    builder.wire([
      { node: left, port: { kind: 'output' } },
      { node: right, port: { kind: 'output' } },
    ])
    const source = builder.build()

    expect(() => applyLambdaHeadStrip(
      source,
      left,
      right,
      { commonArity: 1, left: [0, 0], right: [0] },
    )).toThrow(/column 0.*different host wires/i)
  })

  it('requires the two outputs to be one local binary equation', () => {
    const builder = new DiagramBuilder()
    const left = builder.term(builder.root, lambda(application(bound(0), free(0))))
    const right = builder.term(builder.root, lambda(application(bound(0), free(0))))
    const source = builder.build()
    expect(wireAt(source, left, { kind: 'output' }))
      .not.toBe(wireAt(source, right, { kind: 'output' }))
    expect(() => applyLambdaHeadStrip(
      source,
      left,
      right,
      { commonArity: 1, left: [0], right: [0] },
    )).toThrow(/share one wire/i)
  })
})
