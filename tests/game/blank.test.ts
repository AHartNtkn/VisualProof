import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { blankDiagram, isBlank, assertClosedGoal } from '../../src/game/blank'
import { twoVeils } from './fixtures'

describe('game blank authority', () => {
  it('recognizes blank canonically and rejects nonblank diagrams', () => {
    expect(isBlank(blankDiagram())).toBe(true)
    expect(isBlank(twoVeils().goal.diagram)).toBe(false)
  })

  it('accepts only zero-boundary puzzle goals', () => {
    const b = new DiagramBuilder()
    const wire = b.wire(b.root, [])
    expect(() => assertClosedGoal(mkDiagramWithBoundary(b.build(), [wire])))
      .toThrow(/puzzle goal must be closed/)
    expect(() => assertClosedGoal(twoVeils().goal)).not.toThrow()
  })
})
