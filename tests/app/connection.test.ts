import { describe, expect, it } from 'vitest'
import { joinWires } from '../../src/app/edit'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'

describe('structural connection commit', () => {
  it('identifies two homogeneous wires without term interpretation', () => {
    const builder = new DiagramBuilder()
    const left = builder.wire(builder.root, [])
    const right = builder.wire(builder.root, [])
    const joined = joinWires(builder.build(), [right, left])
    expect(Object.keys(joined.wires)).toEqual([left])
  })
})
