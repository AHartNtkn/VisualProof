import { describe, expect, it } from 'vitest'
import {
  TutorialSession,
  orderTutorialGate,
  toolTutorialGate,
  type TutorialEvent,
  type TutorialMilestoneId,
} from '../../src/game/tutorial'

function observe(session: TutorialSession, event: TutorialEvent): readonly TutorialMilestoneId[] {
  return session.observe(event).newlyCompleted
}

describe('TutorialSession', () => {
  it('advances the opening sequence from committed events and exposes one instruction', () => {
    const session = new TutorialSession()

    expect(session.currentInstruction?.milestoneId).toBe('move')
    expect(observe(session, { kind: 'tree-selected' })).toEqual([])
    expect(observe(session, { kind: 'camera-capability', capability: 'look' })).toEqual([])

    expect(observe(session, { kind: 'camera-capability', capability: 'move' })).toEqual(['move'])
    expect(session.currentInstruction?.milestoneId).toBe('look')
    expect(observe(session, { kind: 'camera-capability', capability: 'look' })).toEqual(['look'])
    expect(observe(session, { kind: 'camera-capability', capability: 'ascend' })).toEqual(['ascend'])
    expect(observe(session, { kind: 'camera-capability', capability: 'descend' })).toEqual(['descend'])
    expect(observe(session, { kind: 'camera-capability', capability: 'sprint' })).toEqual(['sprint'])
    expect(session.currentInstruction?.milestoneId).toBe('select-tree')

    expect(observe(session, { kind: 'tree-selected' })).toEqual(['select-tree'])
    expect(observe(session, { kind: 'orbit-moved' })).toEqual(['move-orbit'])
    expect(observe(session, { kind: 'orbit-exited' })).toEqual(['exit-orbit'])
    expect(session.currentInstruction?.milestoneId).toBe('spawn-two-sprouts')

    expect(observe(session, { kind: 'sprout-spawned', blankTreeCount: 2 })).toEqual([])
    expect(observe(session, { kind: 'sprout-spawned', blankTreeCount: 3 })).toEqual(['spawn-two-sprouts'])
    expect(observe(session, { kind: 'tool-acquired', toolId: 'iteration' })).toEqual([])
    expect(observe(session, { kind: 'tool-acquired', toolId: 'double-cut' })).toEqual(['acquire-double-cut'])
    expect(observe(session, { kind: 'double-cut-applied' })).toEqual(['apply-double-cut'])
    expect(session.currentInstruction?.milestoneId).toBe('double-cut-explained')
    expect(observe(session, { kind: 'ledger-opened' })).toEqual(['double-cut-explained'])
    expect(observe(session, { kind: 'tool-acquired', toolId: 'iteration' })).toEqual(['acquire-iteration'])
    expect(observe(session, { kind: 'nonblank-tree-duplicated' })).toEqual(['duplicate-nonblank'])
    expect(session.currentInstruction?.milestoneId).toBe('complete-blank-order')
  })

  it('treats disabled tutorials as passing gates without manufacturing completion', () => {
    const session = new TutorialSession()

    session.setEnabled(false)
    expect(([
      'spawn-two-sprouts',
      'double-cut-explained',
      'duplicate-nonblank',
      'complete-single-double-cut-order',
    ] as const).every((milestoneId) => session.check(milestoneId))).toBe(true)
    expect(session.check('acquire-double-cut')).toBe(true)
    expect(session.completed.has('acquire-double-cut')).toBe(false)

    expect(observe(session, { kind: 'tool-acquired', toolId: 'double-cut' })).toEqual([])
    expect(session.completed.has('acquire-double-cut')).toBe(false)

    completeThroughSpawn(session)
    session.setEnabled(false)
    expect(session.check('acquire-double-cut')).toBe(true)
    expect(session.completed.has('acquire-double-cut')).toBe(false)

    expect(observe(session, { kind: 'tool-acquired', toolId: 'double-cut' })).toEqual(['acquire-double-cut'])
    expect(session.completed.has('acquire-double-cut')).toBe(true)
    session.setEnabled(true)
    expect(session.currentInstruction?.milestoneId).not.toBe('acquire-double-cut')
  })

  it('hides the card after the blank order while completing silent orders in either final-order sequence', () => {
    for (const [first, second, firstMilestone, secondMilestone] of [
      [
        'irregular-double-cut-a',
        'irregular-double-cut-b',
        'complete-irregular-double-cut-a-order',
        'complete-irregular-double-cut-b-order',
      ],
      [
        'irregular-double-cut-b',
        'irregular-double-cut-a',
        'complete-irregular-double-cut-b-order',
        'complete-irregular-double-cut-a-order',
      ],
    ] as const) {
      const session = new TutorialSession()
      completeThroughDuplication(session)

      expect(observe(session, { kind: 'order-completed', orderId: 'single-double-cut' })).toEqual([])
      expect(observe(session, { kind: 'order-completed', orderId: 'blank-sprout' })).toEqual(['complete-blank-order'])
      expect(session.currentInstruction).toBeNull()
      expect(observe(session, { kind: 'order-completed', orderId: 'single-double-cut' })).toEqual(['complete-single-double-cut-order'])
      expect(observe(session, { kind: 'order-completed', orderId: first })).toEqual([firstMilestone])
      expect(observe(session, { kind: 'order-completed', orderId: second })).toEqual([secondMilestone])
      expect(session.completed.has('complete-irregular-double-cut-a-order')).toBe(true)
      expect(session.completed.has('complete-irregular-double-cut-b-order')).toBe(true)
      expect(session.currentInstruction).toBeNull()
    }
  })

  it('maps only the opening tutorial gates onto tools and orders', () => {
    expect(toolTutorialGate('sprout-spawner')).toBeNull()
    expect(toolTutorialGate('double-cut')).toBe('spawn-two-sprouts')
    expect(toolTutorialGate('iteration')).toBe('double-cut-explained')
    expect(toolTutorialGate('other')).toBeNull()

    expect(orderTutorialGate('blank-sprout')).toBe('duplicate-nonblank')
    expect(orderTutorialGate('single-double-cut')).toBeNull()
    expect(orderTutorialGate('irregular-double-cut-a')).toBeNull()
    expect(orderTutorialGate('irregular-double-cut-b')).toBeNull()
    expect(orderTutorialGate('other')).toBeNull()
  })
})

function completeThroughSpawn(session: TutorialSession): void {
  observe(session, { kind: 'camera-capability', capability: 'move' })
  observe(session, { kind: 'camera-capability', capability: 'look' })
  observe(session, { kind: 'camera-capability', capability: 'ascend' })
  observe(session, { kind: 'camera-capability', capability: 'descend' })
  observe(session, { kind: 'camera-capability', capability: 'sprint' })
  observe(session, { kind: 'tree-selected' })
  observe(session, { kind: 'orbit-moved' })
  observe(session, { kind: 'orbit-exited' })
  observe(session, { kind: 'sprout-spawned', blankTreeCount: 3 })
}

function completeThroughDuplication(session: TutorialSession): void {
  completeThroughSpawn(session)
  observe(session, { kind: 'tool-acquired', toolId: 'double-cut' })
  observe(session, { kind: 'double-cut-applied' })
  observe(session, { kind: 'ledger-opened' })
  observe(session, { kind: 'tool-acquired', toolId: 'iteration' })
  observe(session, { kind: 'nonblank-tree-duplicated' })
}
