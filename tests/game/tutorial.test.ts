import { describe, expect, it } from 'vitest'
import {
  TutorialSession,
  orderTutorialGate,
  toolTutorialGate,
  type TutorialEvent,
  type TutorialMilestoneId,
} from '../../src/game/tutorial'
import { LiveTutorialContent, decodeTutorialContent, openingTutorialContent } from '../../src/game/tutorial/content'
import { readFileSync } from 'node:fs'

function observe(session: TutorialSession, event: TutorialEvent): readonly TutorialMilestoneId[] {
  return session.observe(event).newlyCompleted
}

describe('TutorialSession', () => {
  it('keeps tutorial progression keyed by milestone IDs when live copy changes', () => {
    // Catches progression comparing replaceable tutorial prose instead of semantic milestones.
    const records: Array<Record<string, unknown>> = JSON.parse(readFileSync(
      new URL('../../game/content/tutorial.json', import.meta.url),
      'utf8',
    ))
    records[0]!['text'] = 'Walk using W/A/S/D.'
    const content = new LiveTutorialContent(decodeTutorialContent(records))
    const session = new TutorialSession(true, [], content)

    expect(session.currentInstruction).toEqual({ milestoneId: 'move', text: 'Walk using W/A/S/D.' })
    expect(observe(session, { kind: 'camera-capability', capability: 'move' })).toEqual(['move'])
    expect(session.currentInstruction?.milestoneId).toBe('look')
    expect(openingTutorialContent.current.definition('move').text).not.toBe('Walk using W/A/S/D.')
  })
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
    expect(session.currentInstruction).toBeNull()

    expect(observe(session, { kind: 'tool-acquired', toolId: 'double-cut' })).toEqual([
      'acquire-double-cut',
    ])
    expect(session.completed.has('acquire-double-cut')).toBe(true)

    session.setEnabled(true)
    expect(session.currentInstruction?.milestoneId).toBe('move')
  })

  it('completes repeatable accomplishments immediately while presenting the first unfinished step', () => {
    const session = new TutorialSession(false)

    expect(observe(session, { kind: 'sprout-spawned', blankTreeCount: 3 })).toEqual([
      'spawn-two-sprouts',
    ])
    expect(observe(session, { kind: 'double-cut-applied' })).toEqual(['apply-double-cut'])
    expect(observe(session, { kind: 'nonblank-tree-duplicated' })).toEqual([
      'duplicate-nonblank',
    ])
    session.setEnabled(true)

    expect(session.currentInstruction?.milestoneId).toBe('move')
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
    expect(observe(beforeSave, { kind: 'tool-acquired', toolId: 'double-cut' })).toEqual([
      'acquire-double-cut',
    ])

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

    expect(commit).toEqual(['spawn-two-sprouts'])
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
    expect(observe(beforeSave, { kind: 'order-completed', orderId: 'blank-sprout' })).toEqual([
      'complete-blank-order',
    ])
    expect(observe(beforeSave, { kind: 'order-completed', orderId: 'single-double-cut' })).toEqual([
      'complete-single-double-cut-order',
    ])

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

    expect(commit).toEqual(['duplicate-nonblank'])
    expect(reconstructed.currentInstruction).toBeNull()
  })

  it('reconstructs irreversible progress without inferring repeatable actions', () => {
    const session = new TutorialSession(false)

    expect(session.reconcileDurableProgress({
      acquiredToolIds: new Set(['sprout-spawner', 'double-cut', 'iteration']),
      orders: new Map([
        ['blank-sprout', { kind: 'completed' }],
        ['single-double-cut', { kind: 'completed' }],
        ['irregular-double-cut-a', { kind: 'completed' }],
        ['irregular-double-cut-b', { kind: 'completed' }],
      ]),
    }).newlyCompleted).toEqual([
      'acquire-double-cut',
      'acquire-iteration',
      'complete-blank-order',
      'complete-single-double-cut-order',
      'complete-irregular-double-cut-a-order',
      'complete-irregular-double-cut-b-order',
    ])
    expect(session.completed.has('spawn-two-sprouts')).toBe(false)
    expect(session.completed.has('apply-double-cut')).toBe(false)
    expect(session.completed.has('double-cut-explained')).toBe(false)
    expect(session.completed.has('duplicate-nonblank')).toBe(false)
  })

  it('does not treat a ledger visit before Double Cut as its explanation', () => {
    const session = new TutorialSession(false)

    expect(observe(session, { kind: 'ledger-opened' })).toEqual([])
    expect(session.completed.has('double-cut-explained')).toBe(false)
    expect(observe(session, { kind: 'double-cut-applied' })).toEqual(['apply-double-cut'])
    expect(observe(session, { kind: 'ledger-opened' })).toEqual(['double-cut-explained'])
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

      expect(observe(session, { kind: 'order-completed', orderId: 'single-double-cut' })).toEqual([
        'complete-single-double-cut-order',
      ])
      expect(observe(session, { kind: 'order-completed', orderId: 'blank-sprout' })).toEqual([
        'complete-blank-order',
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
