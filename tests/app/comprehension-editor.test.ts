import { describe, expect, it } from 'vitest'
import {
  applyComprehensionConnection,
  beginComprehensionDraft,
  comprehensionFixture,
} from '../../src/app/comprehension-draft'
import {
  connectionTargets,
  formalBoundaryMarks,
  moveComprehensionEditor,
  placeComprehensionEditor,
  resizeComprehensionEditor,
} from '../../src/app/comprehension-editor'

describe('comprehension editor window geometry', () => {
  it('opens to the right of the invocation when possible and falls back left', () => {
    expect(placeComprehensionEditor({ x: 300, y: 300 }, { width: 1400, height: 900 })).toEqual({
      left: 316, top: 282, width: 660, height: 560,
    })
    expect(placeComprehensionEditor({ x: 1200, y: 300 }, { width: 1400, height: 900 })).toEqual({
      left: 524, top: 282, width: 660, height: 560,
    })
  })

  it('clamps narrow placement, movement, and resizing without making the window unreachable', () => {
    expect(placeComprehensionEditor({ x: 10, y: 10 }, { width: 400, height: 360 })).toEqual({
      left: 12, top: 44, width: 376, height: 282,
    })
    const base = { left: 200, top: 100, width: 500, height: 400 }
    expect(moveComprehensionEditor(base, { x: 999, y: -999 }, { width: 900, height: 700 })).toEqual({
      left: 400, top: 0, width: 500, height: 400,
    })
    expect(resizeComprehensionEditor(base, { x: -999, y: 999 }, { width: 900, height: 700 })).toEqual({
      left: 200, top: 100, width: 420, height: 600,
    })
  })
})

describe('comprehension editor boundary and connection presentation', () => {
  it('marks only formal position zero as the orientation reference', () => {
    expect(formalBoundaryMarks(['arg1', 'arg1', 'arg3'])).toEqual([
      { wire: 'arg1', position: 0, orientation: true },
      { wire: 'arg1', position: 1, orientation: false },
      { wire: 'arg3', position: 2, orientation: false },
    ])
  })

  it('derives both target surfaces solely from the checked planner and reuses one host identity', () => {
    const fixture = comprehensionFixture()
    const start = beginComprehensionDraft(fixture.diagram, fixture.bubble)
    const hostSource = { kind: 'host' as const, wire: fixture.parameter }
    const initial = connectionTargets(start, hostSource)
    expect([...initial.draft]).toEqual(['arg1', 'arg2'])
    expect([...initial.host]).toEqual([])

    const bound = applyComprehensionConnection(start, hostSource, { kind: 'draft', wire: 'arg1' })
    const reused = connectionTargets(bound, hostSource)
    expect([...reused.draft]).toEqual(['arg2'])
    expect([...reused.host]).toEqual([])

    const draftSource = { kind: 'draft' as const, wire: 'arg2' }
    const fromDraft = connectionTargets(bound, draftSource)
    expect([...fromDraft.draft]).toContain('arg1')
    expect([...fromDraft.host]).toContain(fixture.parameter)
  })
})
