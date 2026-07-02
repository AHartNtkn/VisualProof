import { describe, it, expect } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { buildScene, initialState, settle, renderScene, DEFAULT_PARAMS } from '../../src/view/index'

describe('reference-node rendering', () => {
  it('renders the defId as a center glyph label, the same channel constants use', () => {
    const b = new DiagramBuilder()
    b.ref(b.root, 'Nat', 1)
    const d = b.build()
    const s = settle(d, initialState(d), DEFAULT_PARAMS, 20000)
    const labels = renderScene(buildScene(d, s.positions)).filter((sh) => sh.kind === 'label')
    expect(labels).toHaveLength(1)
    expect(labels[0]!.kind === 'label' && labels[0]!.text).toBe('Nat')
  })

  it('an arity-0 reference still renders its label (a sentential relation)', () => {
    const b = new DiagramBuilder()
    b.ref(b.root, 'Even', 0)
    const d = b.build()
    const s = settle(d, initialState(d), DEFAULT_PARAMS, 20000)
    const labels = renderScene(buildScene(d, s.positions)).filter((sh) => sh.kind === 'label')
    expect(labels).toHaveLength(1)
    expect(labels[0]!.kind === 'label' && labels[0]!.text).toBe('Even')
  })
})
