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
    expect(session.check('acquire-double-cut')).toBe(true)
    expect(session.completed.has('acquire-double-cut')).toBe(true)
    session.setEnabled(true)
    expect(session.currentInstruction?.milestoneId).not.toBe('acquire-double-cut')
  })

  it('retains early committed evidence and cascades it when prerequisites later complete', () => {
    // Catches unchecked creation or early ungated acquisition erasing legitimate tutorial progress.
    const session = new TutorialSession(false)

    expect(observe(session, { kind: 'tool-acquired', toolId: 'double-cut' })).toEqual([])
    expect(session.completed.has('acquire-double-cut')).toBe(false)
    session.setEnabled(true)
    expect(session.completed.has('acquire-double-cut')).toBe(false)

    const finalCommit = completeThroughSpawn(session)

    expect(finalCommit).toEqual(['spawn-two-sprouts', 'acquire-double-cut'])
    expect(session.completed.has('acquire-double-cut')).toBe(true)
    expect(session.currentInstruction?.milestoneId).toBe('apply-double-cut')
  })

  it('reconstructs early acquired-tool evidence from durable progress without repeating acquisition', () => {
    // Catches a load replacing legitimate early acquisition evidence with only completed milestone IDs.
    const completedBeforeSpawn = [
      'move',
      'look',
      'ascend',
      'descend',
      'sprint',
      'select-tree',
      'move-orbit',
      'exit-orbit',
    ] as const
    const beforeSave = new TutorialSession(false, completedBeforeSpawn)
    expect(observe(beforeSave, { kind: 'tool-acquired', toolId: 'double-cut' })).toEqual([])

    const reconstructed = new TutorialSession(false, beforeSave.completed)
    expect(reconstructed.reconcileDurableProgress({
      acquiredToolIds: new Set(['sprout-spawner', 'double-cut']),
      orders: new Map([
        ['blank-sprout', { kind: 'pending' }],
        ['single-double-cut', { kind: 'pending' }],
        ['irregular-double-cut-a', { kind: 'pending' }],
        ['irregular-double-cut-b', { kind: 'pending' }],
      ]),
    }).newlyCompleted).toEqual([])

    reconstructed.setEnabled(true)
    const commit = observe(reconstructed, { kind: 'sprout-spawned', blankTreeCount: 3 })

    expect(commit).toEqual(['spawn-two-sprouts', 'acquire-double-cut'])
    expect(reconstructed.completed.has('acquire-double-cut')).toBe(true)
  })

  it('reconstructs completed-order evidence without inferring repeatable action milestones', () => {
    // Catches load-time reconstruction either losing order completion or manufacturing camera/tool actions.
    const completedThroughIteration = [
      'move',
      'look',
      'ascend',
      'descend',
      'sprint',
      'select-tree',
      'move-orbit',
      'exit-orbit',
      'spawn-two-sprouts',
      'acquire-double-cut',
      'apply-double-cut',
      'double-cut-explained',
      'acquire-iteration',
    ] as const
    const beforeSave = new TutorialSession(false, completedThroughIteration)
    expect(observe(beforeSave, { kind: 'order-completed', orderId: 'blank-sprout' })).toEqual([])
    expect(observe(beforeSave, { kind: 'order-completed', orderId: 'single-double-cut' })).toEqual([])

    const reconstructed = new TutorialSession(false, beforeSave.completed)
    expect(reconstructed.reconcileDurableProgress({
      acquiredToolIds: new Set(['sprout-spawner', 'double-cut', 'iteration']),
      orders: new Map([
        ['blank-sprout', { kind: 'completed' }],
        ['single-double-cut', { kind: 'completed' }],
        ['irregular-double-cut-a', { kind: 'pending' }],
        ['irregular-double-cut-b', { kind: 'pending' }],
      ]),
    }).newlyCompleted).toEqual([])
    expect(reconstructed.completed.has('duplicate-nonblank')).toBe(false)

    reconstructed.setEnabled(true)
    const commit = observe(reconstructed, { kind: 'nonblank-tree-duplicated' })

    expect(commit).toEqual([
      'duplicate-nonblank',
      'complete-blank-order',
      'complete-single-double-cut-order',
    ])
  })

  it('does not infer repeatable tutorial actions from durable tools and orders alone', () => {
    // Catches reconstruction treating unrelated durable state as proof of camera or tree actions.
    const session = new TutorialSession(false)

    expect(session.reconcileDurableProgress({
      acquiredToolIds: new Set(['sprout-spawner', 'double-cut', 'iteration']),
      orders: new Map([
        ['blank-sprout', { kind: 'completed' }],
        ['single-double-cut', { kind: 'completed' }],
        ['irregular-double-cut-a', { kind: 'completed' }],
        ['irregular-double-cut-b', { kind: 'completed' }],
      ]),
    }).newlyCompleted).toEqual([])
    expect([...session.completed]).toEqual([])
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
      expect(observe(session, { kind: 'order-completed', orderId: 'blank-sprout' })).toEqual([
        'complete-blank-order',
        'complete-single-double-cut-order',
      ])
      expect(session.currentInstruction).toBeNull()
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

function completeThroughSpawn(session: TutorialSession): readonly TutorialMilestoneId[] {
  observe(session, { kind: 'camera-capability', capability: 'move' })
  observe(session, { kind: 'camera-capability', capability: 'look' })
  observe(session, { kind: 'camera-capability', capability: 'ascend' })
  observe(session, { kind: 'camera-capability', capability: 'descend' })
  observe(session, { kind: 'camera-capability', capability: 'sprint' })
  observe(session, { kind: 'tree-selected' })
  observe(session, { kind: 'orbit-moved' })
  observe(session, { kind: 'orbit-exited' })
  return observe(session, { kind: 'sprout-spawned', blankTreeCount: 3 })
}

function completeThroughDuplication(session: TutorialSession): void {
  completeThroughSpawn(session)
  observe(session, { kind: 'tool-acquired', toolId: 'double-cut' })
  observe(session, { kind: 'double-cut-applied' })
  observe(session, { kind: 'ledger-opened' })
  observe(session, { kind: 'tool-acquired', toolId: 'iteration' })
  observe(session, { kind: 'nonblank-tree-duplicated' })
}
