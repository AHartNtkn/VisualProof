import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { bvar, lam, port } from '../../../src/kernel/term/term'
import { anchorAvailability } from '../../../src/kernel/rules/anchored-wire'

const CLOSED = lam(bvar(0))

describe('anchorAvailability', () => {
  it('crosses bubbles to the witness wire scope', () => {
    const b = new DiagramBuilder()
    const outer = b.bubble(b.root, 1)
    const inner = b.bubble(outer, 1)
    const witness = b.termNode(inner, CLOSED)
    b.wire(b.root, [{ node: witness, port: { kind: 'output' } }])
    expect(anchorAvailability(b.build(), witness)).toBe(b.root)
  })

  it('stops inside the first enclosing cut', () => {
    const b = new DiagramBuilder()
    const cut = b.cut(b.root)
    const bubble = b.bubble(cut, 1)
    const witness = b.termNode(bubble, CLOSED)
    b.wire(b.root, [{ node: witness, port: { kind: 'output' } }])
    expect(anchorAvailability(b.build(), witness)).toBe(cut)
  })

  it('never walks above the output wire scope', () => {
    const b = new DiagramBuilder()
    const scope = b.bubble(b.root, 1)
    const inner = b.bubble(scope, 1)
    const witness = b.termNode(inner, CLOSED)
    b.wire(scope, [{ node: witness, port: { kind: 'output' } }])
    expect(anchorAvailability(b.build(), witness)).toBe(scope)
  })

  it('refuses open and non-term witnesses', () => {
    const b = new DiagramBuilder()
    const open = b.termNode(b.root, port('x'))
    const ref = b.ref(b.root, 'R', 0)
    b.wire(b.root, [{ node: open, port: { kind: 'output' } }])
    expect(() => anchorAvailability(b.build(), open)).toThrow(/closed witness/)
    expect(() => anchorAvailability(b.build(), ref)).toThrow(/term nodes/)
  })
})
