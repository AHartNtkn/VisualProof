import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { applyErasure, applyWireSever } from '../../../src/kernel/rules/erasure'

const p = (s: string) => parseTerm(s)

describe('applyErasure', () => {
  it('removes a selection from a positive region', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('\\x. x'))
    const cut = h.cut(h.root)
    h.termNode(cut, p('\\x. \\y. x'))
    const host = h.build()
    const sel = mkSelection(host, { region: host.root, regions: [], nodes: [n], wires: [] })
    const out = applyErasure(host, sel)
    expect(out.nodes[n]).toBeUndefined()
    expect(Object.keys(out.regions)).toHaveLength(2) // the cut survives
  })

  it('erases whole subtrees from doubly-cut (positive) regions', () => {
    const h = new DiagramBuilder()
    const cut1 = h.cut(h.root)
    const cut2 = h.cut(cut1)
    const inner = h.cut(cut2)
    h.termNode(inner, p('\\x. x'))
    const host = h.build()
    const sel = mkSelection(host, { region: cut2, regions: [inner], nodes: [], wires: [] })
    const out = applyErasure(host, sel)
    expect(out.regions[inner]).toBeUndefined()
  })

  it('rejects negative regions by name', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const n = h.termNode(cut, p('\\x. x'))
    const host = h.build()
    const sel = mkSelection(host, { region: cut, regions: [], nodes: [n], wires: [] })
    expect(() => applyErasure(host, sel))
      .toThrowError(/erasure requires a positive region; 'r1' is negative/)
  })
})

describe('applyWireSever', () => {
  it('splits a wire into two at the same positive scope', () => {
    const h = new DiagramBuilder()
    const n1 = h.termNode(h.root, p('\\x. x'))
    const n2 = h.termNode(h.root, p('\\x. \\y. x'))
    const w = h.wire(h.root, [
      { node: n1, port: { kind: 'output' } },
      { node: n2, port: { kind: 'output' } },
    ])
    const host = h.build()
    const out = applyWireSever(host, w, [{ node: n1, port: { kind: 'output' } }])
    expect(out.wires[w]?.endpoints).toHaveLength(1)
    expect(out.wires[w]?.endpoints[0]?.node).toBe(n1)
    const newWires = Object.keys(out.wires).filter((id) => host.wires[id] === undefined)
    expect(newWires).toHaveLength(1)
    expect(out.wires[newWires[0]!]?.endpoints).toHaveLength(1)
    expect(out.wires[newWires[0]!]?.scope).toBe(host.root)
  })

  it('creates the fresh wire at the original scope, not the root', () => {
    const h = new DiagramBuilder()
    const cut1 = h.cut(h.root)
    const cut2 = h.cut(cut1)
    const n1 = h.termNode(cut2, p('\\x. x'))
    const n2 = h.termNode(cut2, p('\\x. \\y. x'))
    const w = h.wire(cut2, [
      { node: n1, port: { kind: 'output' } },
      { node: n2, port: { kind: 'output' } },
    ])
    const host = h.build()
    const out = applyWireSever(host, w, [{ node: n1, port: { kind: 'output' } }])
    const newWires = Object.keys(out.wires).filter((id) => host.wires[id] === undefined)
    expect(newWires).toHaveLength(1)
    expect(out.wires[newWires[0]!]?.scope).toBe(cut2)
    expect(out.wires[w]?.scope).toBe(cut2)
  })

  it('rejects severing at negative scopes by name', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const n1 = h.termNode(cut, p('\\x. x'))
    const w = h.wire(cut, [{ node: n1, port: { kind: 'output' } }])
    const host = h.build()
    expect(() => applyWireSever(host, w, []))
      .toThrowError(/severing a wire requires a positive scope; 'r1' is negative/)
  })

  it('rejects keep-entries that are not endpoints of the wire', () => {
    const h = new DiagramBuilder()
    const n1 = h.termNode(h.root, p('\\x. x'))
    const w = h.wire(h.root, [{ node: n1, port: { kind: 'output' } }])
    const host = h.build()
    expect(() => applyWireSever(host, w, [{ node: 'ghost', port: { kind: 'output' } }]))
      .toThrowError(/'ghost'.*is not an endpoint of wire 'w0'/)
  })
})
