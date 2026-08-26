import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { wireAt } from '../../../src/kernel/rules/access'
import {
  anchorAvailability,
  applyLambdaAnchoredWireContract,
  applyLambdaAnchoredWireSplit,
} from '../../../src/kernel/rules/lambda/anchored-wire'
import { bound, free, lambda } from '../../../src/kernel/term/term'

describe('Lambda anchored wire split and contract', () => {
  it('moves a chosen endpoint onto a target-scoped duplicate closed witness', () => {
    const builder = new DiagramBuilder()
    const target = builder.cut(builder.root)
    const witness = builder.term(builder.root, lambda(bound(0)))
    const consumer = builder.term(target, free(0))
    const moved = { node: consumer, port: { kind: 'free' as const, index: 0 } }
    const wire = builder.wire([
      { node: witness, port: { kind: 'output' } },
      moved,
    ])
    const source = builder.build()

    expect(anchorAvailability(source, witness)).toBe(builder.root)
    const split = applyLambdaAnchoredWireSplit(
      source,
      wire,
      witness,
      [moved],
      target,
    )
    const duplicate = Object.keys(split.nodes).find((id) => source.nodes[id] === undefined)!
    const duplicateWire = wireAt(split, duplicate, { kind: 'output' })
    expect(duplicateWire).not.toBe(wire)
    expect(split.wires[duplicateWire]!.endpoints).toContainEqual(moved)

    const contracted = applyLambdaAnchoredWireContract(
      split,
      duplicate,
      witness,
      { leftSteps: [], rightSteps: [] },
    )
    expect(contracted.nodes[duplicate]).toBeUndefined()
    expect(contracted.wires[duplicateWire]).toBeUndefined()
    expect(contracted.wires[wire]!.endpoints).toContainEqual(moved)
  })

  it('rejects open witnesses', () => {
    const builder = new DiagramBuilder()
    const witness = builder.term(builder.root, free(0))
    const source = builder.build()
    expect(() => anchorAvailability(source, witness)).toThrow(/closed witness/i)
  })
})
