import { describe, expect, it } from 'vitest'
import type { Hit } from '../../src/interaction/hittest'
import {
  choosePointerPhase,
  createBrushState,
  isHitSelected,
  reduceBrush,
  type BrushMode,
} from '../../src/interaction/controllers/brush'

const nodeA: Hit = { kind: 'node', id: 'a' }
const nodeB: Hit = { kind: 'node', id: 'b' }
const wire: Hit = { kind: 'wire', id: 'w' }

const click = (
  selected: readonly Hit[],
  hit: Hit | null,
  mode: BrushMode,
): readonly Hit[] => {
  const begun = reduceBrush(createBrushState(selected), { kind: 'begin', hit, mode })
  return reduceBrush(begun, { kind: 'end' }).selected
}

const drag = (
  selected: readonly Hit[],
  hits: readonly (Hit | null)[],
  mode: BrushMode,
): readonly Hit[] => {
  const [first = null, ...rest] = hits
  let state = reduceBrush(createBrushState(selected), { kind: 'begin', hit: first, mode })
  for (const hit of rest) state = reduceBrush(state, { kind: 'move', hit })
  return reduceBrush(state, { kind: 'end' }).selected
}

describe('game proof selection brush', () => {
  it('plain click selects an unselected hit and preserves a selected hit', () => {
    expect(click([], nodeA, 'select')).toEqual([nodeA])
    expect(click([nodeA], nodeA, 'select')).toEqual([nodeA])
  })

  it('Shift-mode click deselects a selected hit and never selects an unselected hit', () => {
    expect(click([nodeA], nodeA, 'deselect')).toEqual([])
    expect(click([], nodeA, 'deselect')).toEqual([])
  })

  it('plain drag adds crossed hits while Shift-mode drag only deselects crossed hits', () => {
    expect(drag([nodeA], [nodeA, nodeB, wire], 'select')).toEqual([nodeA, nodeB, wire])
    expect(drag([nodeA, wire], [nodeA, nodeB, wire], 'deselect')).toEqual([])
  })

  it('clears only a still background click and keeps a moved void-start stroke additive', () => {
    expect(click([nodeA, wire], null, 'select')).toEqual([])
    expect(drag([wire], [null, nodeA, null, nodeB], 'select')).toEqual([wire, nodeA, nodeB])
  })

  it('deduplicates semantic hits and keeps selection vocabulary distinct from proof erasure', () => {
    const state = drag([nodeA, nodeA], [nodeB, nodeB], 'select')
    expect(state).toEqual([nodeA, nodeB])
    expect(isHitSelected(state, { kind: 'node', id: 'b' })).toBe(true)
    expect(isHitSelected(state, { kind: 'wire', id: 'b' })).toBe(false)
  })
})

describe('game pointer phase precedence', () => {
  it('keeps Shift selection-only ahead of Ctrl and proof claims', () => {
    expect(choosePointerPhase({ shiftKey: true, ctrlKey: true }, true)).toBe('selection')
    expect(choosePointerPhase({ shiftKey: true, ctrlKey: false }, true)).toBe('selection')
  })

  it('chooses physics for Ctrl, then a claim, then selection', () => {
    expect(choosePointerPhase({ shiftKey: false, ctrlKey: true }, true)).toBe('physics')
    expect(choosePointerPhase({ shiftKey: false, ctrlKey: false }, true)).toBe('claimed')
    expect(choosePointerPhase({ shiftKey: false, ctrlKey: false }, false)).toBe('selection')
  })
})
