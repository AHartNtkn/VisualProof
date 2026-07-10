import { describe, it, expect } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkEngine, settle, paint, LIGHT } from '../../src/view/index'
import { referenceDisplayLabel } from '../../src/view/paint'

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

  it('displays the full namespace leaf without changing the qualified semantic id', () => {
    const defId = 'logic/relations/ExtraordinarilyLongPredicate'
    const b = new DiagramBuilder()
    const ref = b.ref(b.root, defId, 0)
    const d = b.build()
    const e = mkEngine(d, [])
    settle(e, 400)

    expect(referenceDisplayLabel(defId)).toBe('ExtraordinarilyLongPredicate')
    expect(d.nodes[ref]!.kind === 'ref' && d.nodes[ref]!.defId).toBe(defId)
    const label = paint(e, LIGHT).find((shape) => shape.kind === 'label')
    expect(label?.kind === 'label' && label.text).toBe('ExtraordinarilyLongPredicate')
  })

  it('displays a long unqualified id in full', () => {
    const defId = 'UnqualifiedRelationWithManyLetters'
    expect(referenceDisplayLabel(defId)).toBe(defId)
  })
})
