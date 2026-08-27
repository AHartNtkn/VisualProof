import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { joinWires } from '../../../src/app/edit'
import { wireAt } from '../../../src/kernel/rules/access'
import {
  proposeAttachedSlotCorrespondence,
  proposeSlotCorrespondence,
  validateSlotCorrespondence,
} from '../../../src/kernel/rules/lambda/correspondence'
import { application, free } from '../../../src/kernel/term/term'

describe('Lambda slot correspondence authoring', () => {
  it('assigns one common column to each distinct carrier across both sides', () => {
    const correspondence = proposeSlotCorrespondence(
      ['shared', 'left', 'shared'],
      ['right', 'shared'],
    )

    expect(() => validateSlotCorrespondence(correspondence, 3, 2)).not.toThrow()
    expect(correspondence.commonArity).toBe(3)
    expect(correspondence.left[0]).toBe(correspondence.left[2])
    expect(correspondence.left[0]).toBe(correspondence.right[1])
    expect(new Set([...correspondence.left, ...correspondence.right]).size).toBe(3)
  })

  it('derives an attached correspondence from the diagram wires', () => {
    const builder = new DiagramBuilder()
    const left = builder.term(builder.root, application(free(0), free(1)), 2)
    const right = builder.term(builder.root, free(0), 1)
    const initial = builder.build()
    const diagram = joinWires(initial, [
      wireAt(initial, left, { kind: 'free', index: 1 }),
      wireAt(initial, right, { kind: 'free', index: 0 }),
    ])

    const correspondence = proposeAttachedSlotCorrespondence(diagram, left, right)
    expect(() => validateSlotCorrespondence(correspondence, 2, 1)).not.toThrow()
    expect(correspondence.commonArity).toBe(2)
    expect(correspondence.left[1]).toBe(correspondence.right[0])
    expect(correspondence.left[0]).not.toBe(correspondence.right[0])
  })
})
