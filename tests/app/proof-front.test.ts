import { describe, expect, it } from 'vitest'
import {
  frontInputAllowed,
  frontKeyRoute,
  retainedFrontIds,
} from '../../src/app/proof-front-policy'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { UNARY } from '../fixtures/zero-signature'

describe('proof-front policy', () => {
  it('routes input only to the focused, enabled front', () => {
    const key = {
      key: 'Home',
      shiftKey: false,
      ctrlKey: false,
      altKey: false,
      metaKey: false,
      repeat: false,
    }
    expect(frontKeyRoute(false, key)).toBeNull()
    expect(frontKeyRoute(true, key)).toBe(key)
    expect(frontInputAllowed(true, true)).toBe(true)
    expect(frontInputAllowed(true, false)).toBe(false)
  })

  it('drops selection and pin IDs absent from the current structural graph', () => {
    const builder = new DiagramBuilder()
    const node = builder.ref(builder.root, 'UnaryWitness', UNARY)
    const diagram = builder.build()
    expect(retainedFrontIds(
      diagram,
      [{ kind: 'node', id: node }, { kind: 'node', id: 'gone' }],
      [node, 'gone'],
    )).toEqual({
      selection: [{ kind: 'node', id: node }],
      pins: [node],
    })
  })
})
