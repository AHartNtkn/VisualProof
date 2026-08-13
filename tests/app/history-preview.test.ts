import { describe, expect, it } from 'vitest'
import { deriveChangeFocus, previewTransition } from '../../src/app/history-preview'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { spawnRefNode } from '../../src/kernel/diagram/spawn'
import { UNARY } from '../fixtures/zero-signature'

describe('history preview focus', () => {
  it('focuses newly added structural nodes and their wires', () => {
    const before = new DiagramBuilder().build()
    const after = spawnRefNode(before, before.root, 'UnaryWitness', UNARY).diagram
    const focus = deriveChangeFocus(before, after)
    expect(focus.kind).toBe('items')
    if (focus.kind === 'items') {
      // The spawned ref, the pin holding its fresh argument wire, and that
      // wire: every end of a new wire is a new node.
      expect(focus.nodes).toHaveLength(2)
      expect(focus.wires).toHaveLength(1)
    }
  })

  it('falls back to the whole diagram when no structure changed', () => {
    const diagram = new DiagramBuilder().build()
    expect(deriveChangeFocus(diagram, diagram)).toEqual({ kind: 'diagram' })
    expect(previewTransition([diagram], 50)).toEqual({
      before: diagram,
      after: diagram,
      focus: { kind: 'diagram' },
    })
  })
})
