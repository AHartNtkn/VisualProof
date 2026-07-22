import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import {
  applyComprehensionConnection,
  beginComprehensionDraft,
  currentComprehensionDraft,
  moveComprehensionHistory,
  replaceComprehensionDiagram,
} from '../../src/game/interface/loupe/draft'
import {
  arbitrateConstructionHostClaim,
  applyLoupeConnection,
  constructionLoupeBoundPredicateOptions,
  constructionInstantiationStep,
  connectionTargets,
  resolveConstructionLoupeKey,
} from '../../src/game/interface/construction-loupe'
import {
  addEmptyBubble,
  addEmptyCut,
  addRefNode,
  addTermNode,
} from '../../src/game/interface/loupe/edit'
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
  it('creates empty cut and quantified-bubble children in the requested region', () => {
    const diagram = new DiagramBuilder().build()

    const cut = addEmptyCut(diagram, diagram.root)
    expect(cut.diagram.regions[cut.region]).toEqual({ kind: 'cut', parent: diagram.root })
    expect(Object.values(cut.diagram.nodes).filter((node) => node.region === cut.region)).toEqual([])

    const bubble = addEmptyBubble(cut.diagram, diagram.root, 2)
    expect(bubble.diagram.regions[bubble.region]).toEqual({ kind: 'bubble', parent: diagram.root, arity: 2 })
    expect(Object.values(bubble.diagram.nodes).filter((node) => node.region === bubble.region)).toEqual([])
    expect(() => addEmptyBubble(diagram, diagram.root, -1)).toThrow(/valid arity/)
  })

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
    const step = constructionInstantiationStep(connected)
    expect(step).toMatchObject({
      rule: 'comprehensionInstantiate',
      bubble: fixture.bubble,
      attachments: [fixture.parameter],
    })
    if (step.rule !== 'comprehensionInstantiate') throw new Error('expected construction instantiation')
    expect(step.binders).toEqual([])
  })

  it('keeps draft and host binder menu sources distinct and exposes only strict host ancestors', () => {
    const builder = new DiagramBuilder()
    const outer = builder.bubble(builder.root, 1)
    const guard = builder.cut(outer)
    const inner = builder.bubble(guard, 2)
    const target = builder.bubble(inner, 0)
    const inaccessible = builder.bubble(builder.root, 3)
    const host = builder.build()
    let draft = beginComprehensionDraft(host, target)
    const current = currentComprehensionDraft(draft)
    draft = replaceComprehensionDiagram(draft, {
      ...current.relation.diagram,
      regions: {
        ...current.relation.diagram.regions,
        [outer]: { kind: 'bubble', parent: current.relation.diagram.root, arity: 0 },
      },
    })

    const options = constructionLoupeBoundPredicateOptions(draft, outer)
    expect(options.filter((option) => option.binder === outer)).toEqual([
      { source: 'draft', binder: outer, arity: 0, position: 1, total: 1 },
      { source: 'host', binder: outer, arity: 1, position: 2, total: 2 },
    ])
    expect(options.filter((option) => option.source === 'host')).toEqual([
      { source: 'host', binder: outer, arity: 1, position: 2, total: 2 },
      { source: 'host', binder: inner, arity: 2, position: 1, total: 2 },
    ])
    expect(options.some((option) => option.binder === target || option.binder === inaccessible)).toBe(false)
  })

  it('arbitrates the existing wire claim before selected host-pattern import', () => {
    const wire = {
      still: 'claim' as const, blocksPassiveRelaxation: true,
      move: () => {}, release: () => {}, cancel: () => {},
    }
    const selected = {
      still: 'selection' as const, blocksPassiveRelaxation: false,
      move: () => {}, release: () => {}, cancel: () => {},
    }

    expect(arbitrateConstructionHostClaim(wire, selected)).toBe(wire)
    expect(arbitrateConstructionHostClaim(null, selected)).toBe(selected)
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
