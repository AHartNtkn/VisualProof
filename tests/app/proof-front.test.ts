import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { parseTerm } from '../../src/kernel/term/parse'
import type { KeySample } from '../../src/interaction/controllers/viewport'
import { frontInputAllowed, frontKeyRoute, retainedFrontIds } from '../../src/app/proof-front'

const key: KeySample = {
  key: 'z', shiftKey: false, ctrlKey: true, altKey: false, metaKey: false, repeat: false,
}

describe('proof front routing state', () => {
  it('routes a keyboard sample only through the focused front', () => {
    expect(frontKeyRoute(false, key)).toBeNull()
    expect(frontKeyRoute(true, key)).toBe(key)
  })

  it('admits front input only when focused, idle, and workspace-safe', () => {
    expect(frontInputAllowed(true, false, true)).toBe(true)
    expect(frontInputAllowed(false, false, true)).toBe(false)
    expect(frontInputAllowed(true, true, true)).toBe(false)
    expect(frontInputAllowed(true, false, false)).toBe(false)
  })

  it('retains only selection and pin identities in that front diagram', () => {
    const b = new DiagramBuilder()
    const node = b.termNode(b.root, parseTerm('\\x. x'))
    const diagram = b.build()
    const wire = Object.keys(diagram.wires)[0]!
    expect(retainedFrontIds(
      diagram,
      [
        { kind: 'node', id: node },
        { kind: 'node', id: 'missing-node' },
        { kind: 'region', id: diagram.root },
        { kind: 'wire', id: wire },
        { kind: 'wire', id: 'missing-wire' },
      ],
      [node, 'missing-node'],
    )).toEqual({
      selection: [
        { kind: 'node', id: node },
        { kind: 'region', id: diagram.root },
        { kind: 'wire', id: wire },
      ],
      pins: [node],
    })
  })
})
