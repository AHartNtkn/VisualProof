import { describe, expect, it } from 'vitest'
import {
  applyComprehensionConnection,
  beginComprehensionDraft,
  currentComprehensionDraft,
  moveComprehensionHistory,
  replaceComprehensionDiagram,
} from '../../src/game/interface/loupe/draft'
import {
  applyLoupeConnection,
  constructionInstantiationStep,
  connectionTargets,
  resolveConstructionLoupeKey,
} from '../../src/game/interface/construction-loupe'
import { addRefNode, addTermNode } from '../../src/game/interface/loupe/edit'
import { parseTerm } from '../../src/kernel/term/parse'
import { comprehensionFixture } from '../app/comprehension-fixture'

const key = (value: Partial<{
  key: string
  shiftKey: boolean
  ctrlKey: boolean
  altKey: boolean
  metaKey: boolean
  repeat: boolean
}> = {}) => ({
  key: '', shiftKey: false, ctrlKey: false, altKey: false, metaKey: false, repeat: false, ...value,
})

describe('game-owned construction loupe semantics', () => {
  it('keeps undo and redo inside retained draft history and branches locally', () => {
    const fixture = comprehensionFixture()
    let draft = beginComprehensionDraft(fixture.diagram, fixture.bubble)
    draft = replaceComprehensionDiagram(draft, addTermNode(currentComprehensionDraft(draft).relation.diagram, 'r0', parseTerm('x')).diagram)
    draft = replaceComprehensionDiagram(draft, addRefNode(currentComprehensionDraft(draft).relation.diagram, 'r0', 'library/r', 1).diagram)
    expect([draft.cursor, draft.history.length]).toEqual([2, 3])
    draft = moveComprehensionHistory(draft, -1)
    expect([draft.cursor, draft.history.length]).toEqual([1, 3])
    draft = replaceComprehensionDiagram(draft, addRefNode(currentComprehensionDraft(draft).relation.diagram, 'r0', 'library/branch', 2).diagram)
    expect([draft.cursor, draft.history.length]).toEqual([2, 3])
    expect(Object.values(currentComprehensionDraft(draft).relation.diagram.nodes).some(
      (node) => node.kind === 'ref' && node.defId === 'library/r',
    )).toBe(false)
  })

  it('plans and commits local fusion and exact host-wire attachments without an app editor', () => {
    const fixture = comprehensionFixture()
    const start = beginComprehensionDraft(fixture.diagram, fixture.bubble)
    const source = { kind: 'host' as const, wire: fixture.parameter }
    expect([...connectionTargets(start, source).draft]).toEqual(['arg1', 'arg2'])
    const captured = currentComprehensionDraft(start)
    const connected = applyLoupeConnection(start, captured, source, { kind: 'draft', wire: 'arg1' })
    expect(currentComprehensionDraft(connected).externalWires).toEqual([
      { draftWire: 'arg1', hostWire: fixture.parameter },
    ])
    expect(() => applyLoupeConnection(connected, captured, source, { kind: 'draft', wire: 'arg2' })).toThrow(/draft changed/)
    const fused = applyComprehensionConnection(connected, { kind: 'draft', wire: 'arg1' }, { kind: 'draft', wire: 'arg2' })
    expect(currentComprehensionDraft(fused).relation.boundary).toEqual(['arg1', 'arg1'])
    expect(constructionInstantiationStep(connected)).toMatchObject({
      rule: 'comprehensionInstantiate',
      bubble: fixture.bubble,
      attachments: [fixture.parameter],
      binders: {},
    })
  })

  it('resolves only loupe-local standard shortcuts and ignores repeats', () => {
    expect(resolveConstructionLoupeKey(key({ key: 'Enter' }), false)).toBe('commit')
    expect(resolveConstructionLoupeKey(key({ key: 'Enter', ctrlKey: true }), false)).toBe('commit')
    expect(resolveConstructionLoupeKey(key({ key: 'Escape' }), false)).toBe('close')
    expect(resolveConstructionLoupeKey(key({ key: 'Backspace' }), false)).toBe(null)
    expect(resolveConstructionLoupeKey(key({ key: 'Delete' }), false)).toBe(null)
    expect(resolveConstructionLoupeKey(key({ key: 'Backspace' }), true)).toBe(null)
    expect(resolveConstructionLoupeKey(key({ key: 'Delete' }), true)).toBe(null)
    expect(resolveConstructionLoupeKey(key({ key: 'z', ctrlKey: true }), false)).toBe('undo')
    expect(resolveConstructionLoupeKey(key({ key: 'Z', ctrlKey: true, shiftKey: true }), false)).toBe('redo')
    expect(resolveConstructionLoupeKey(key({ key: 'z', metaKey: true }), false)).toBe('undo')
    expect(resolveConstructionLoupeKey(key({ key: 'z', metaKey: true, shiftKey: true }), false)).toBe('redo')
    expect(resolveConstructionLoupeKey(key({ key: 'z', ctrlKey: true, repeat: true }), false)).toBe(null)
    expect(resolveConstructionLoupeKey(key({ key: 'F' }), false)).toBe(null)
  })
})
