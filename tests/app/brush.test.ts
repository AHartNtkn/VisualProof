import { describe, expect, it } from 'vitest'
import type { Hit } from '../../src/app/hittest'
import {
  choosePointerPhase,
  createBrushState,
  isHitSelected,
  reduceBrush,
} from '../../src/app/interact/brush'

const nodeA: Hit = { kind: 'node', id: 'a' }
const nodeB: Hit = { kind: 'node', id: 'b' }
const wire: Hit = { kind: 'wire', id: 'w' }

function click(selected: readonly Hit[], hit: Hit | null): readonly Hit[] {
  const begun = reduceBrush(createBrushState(selected), { kind: 'begin', hit })
  return reduceBrush(begun, { kind: 'end' }).selected
}

describe('brush selection reducer', () => {
  it('plain clicks toggle exactly one semantic hit without mutating the input state', () => {
    const initial = createBrushState([nodeA])
    const added = reduceBrush(initial, { kind: 'begin', hit: nodeB })
    const finished = reduceBrush(added, { kind: 'end' })

    expect(initial.selected).toEqual([nodeA])
    expect(finished.selected).toEqual([nodeA, nodeB])
    expect(click(finished.selected, nodeA)).toEqual([nodeB])
  })

  it('a still void click clears, but beginning in void does not clear prematurely', () => {
    const initial = createBrushState([nodeA, wire])
    const begun = reduceBrush(initial, { kind: 'begin', hit: null })

    expect(begun.selected).toEqual([nodeA, wire])
    expect(reduceBrush(begun, { kind: 'end' }).selected).toEqual([])
  })

  it('a stroke may begin in void and paints every encountered hit into the selection', () => {
    const initial = createBrushState([wire])
    const begun = reduceBrush(initial, { kind: 'begin', hit: null })
    const overA = reduceBrush(begun, { kind: 'move', hit: nodeA })
    const throughVoid = reduceBrush(overA, { kind: 'move', hit: null })
    const overB = reduceBrush(throughVoid, { kind: 'move', hit: nodeB })
    const finished = reduceBrush(overB, { kind: 'end' })

    expect(finished.selected).toEqual([wire, nodeA, nodeB])
  })

  it('does not treat a void-start stroke across an already-selected hit as a void click', () => {
    const initial = createBrushState([nodeA])
    const begun = reduceBrush(initial, { kind: 'begin', hit: null })
    const touched = reduceBrush(begun, { kind: 'move', hit: nodeA })

    expect(reduceBrush(touched, { kind: 'end' }).selected).toEqual([nodeA])
  })

  it('a stroke beginning on a selected hit erases selected hits and ignores unselected hits', () => {
    const initial = createBrushState([nodeA, wire])
    const begun = reduceBrush(initial, { kind: 'begin', hit: nodeA })
    const unselected = reduceBrush(begun, { kind: 'move', hit: nodeB })
    const selected = reduceBrush(unselected, { kind: 'move', hit: wire })
    const finished = reduceBrush(selected, { kind: 'end' })

    expect(finished.selected).toEqual([])
  })

  it('deduplicates initial selection and repeated brush passes by semantic identity', () => {
    const initial = createBrushState([nodeA, nodeA, wire, wire])
    const begun = reduceBrush(initial, { kind: 'begin', hit: nodeB })
    const again = reduceBrush(begun, { kind: 'move', hit: nodeB })
    const finished = reduceBrush(again, { kind: 'end' })

    expect(initial.selected).toEqual([nodeA, wire])
    expect(finished.selected).toEqual([nodeA, wire, nodeB])
    expect(isHitSelected(finished.selected, { kind: 'node', id: 'b' })).toBe(true)
    expect(isHitSelected(finished.selected, { kind: 'wire', id: 'b' })).toBe(false)
  })

  it('ignores move and end events when no brush stroke is active', () => {
    const initial = createBrushState([nodeA])
    expect(reduceBrush(initial, { kind: 'move', hit: nodeB })).toBe(initial)
    expect(reduceBrush(initial, { kind: 'end' })).toBe(initial)
  })
})

describe('pointer phase precedence', () => {
  it('makes Shift selection-only ahead of Ctrl and gesture claims', () => {
    expect(choosePointerPhase({ shiftKey: true, ctrlKey: true }, true)).toBe('selection')
    expect(choosePointerPhase({ shiftKey: true, ctrlKey: false }, true)).toBe('selection')
  })

  it('chooses physics for Ctrl, then a claim, then selection', () => {
    expect(choosePointerPhase({ shiftKey: false, ctrlKey: true }, true)).toBe('physics')
    expect(choosePointerPhase({ shiftKey: false, ctrlKey: false }, true)).toBe('claimed')
    expect(choosePointerPhase({ shiftKey: false, ctrlKey: false }, false)).toBe('selection')
  })
})
