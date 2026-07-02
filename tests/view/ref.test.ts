import { describe, it, expect } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkEngine, settle, paint, LIGHT } from '../../src/view/index'

describe('reference-node rendering', () => {
  it('renders the defId as a disc label (the named-node vocabulary, never text on anatomy)', () => {
    const b = new DiagramBuilder()
    b.ref(b.root, 'Nat', 1)
    const d = b.build()
    const e = mkEngine(d, [])
    settle(e, 400)
    const labels = paint(e, LIGHT).filter((s) => s.kind === 'label')
    expect(labels).toHaveLength(1)
    expect(labels[0]!.kind === 'label' && labels[0]!.text).toBe('Nat')
  })

  it('an arity-0 reference still renders its label (a sentential relation)', () => {
    const b = new DiagramBuilder()
    b.ref(b.root, 'Even', 0)
    const d = b.build()
    const e = mkEngine(d, [])
    settle(e, 400)
    const labels = paint(e, LIGHT).filter((s) => s.kind === 'label')
    expect(labels).toHaveLength(1)
    expect(labels[0]!.kind === 'label' && labels[0]!.text).toBe('Even')
  })
})
