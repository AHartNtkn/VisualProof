import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkSelection, selectionContents } from '../../../src/kernel/diagram/subgraph/selection'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

// host: sheet contains node nA('y x'), cut C containing node nB('\x. x'),
// wire wShared (scope root) joining nA.v:y with nB.out (crosses into the cut),
// nA.out and nA.v:x auto-wired; plus a bare wire wBare scoped inside C.
function host() {
  const b = new DiagramBuilder()
  const nA = b.termNode(b.root, p('y x'))
  const cut = b.cut(b.root)
  const nB = b.termNode(cut, p('\\x. x'))
  const wShared = b.wire(b.root, [
    { node: nA, port: { kind: 'freeVar', name: 'y' } },
    { node: nB, port: { kind: 'output' } },
  ])
  const wBare = b.wire(cut, [])
  return { d: b.build(), nA, cut, nB, wShared, wBare }
}

describe('mkSelection', () => {
  it('validates region, child subtrees, direct nodes, explicit top-level wires', () => {
    const h = host()
    const sel = mkSelection(h.d, { region: h.d.root, regions: [h.cut], nodes: [h.nA], wires: [] })
    expect(sel.region).toBe(h.d.root)
  })

  it('rejects regions that are not children of the selection region', () => {
    const h = host()
    expect(() => mkSelection(h.d, { region: h.cut, regions: [h.cut], nodes: [], wires: [] }))
      .toThrowError(/region 'r1' is not a child of selection region 'r1'/)
  })

  it('rejects nodes not directly in the selection region, duplicates, and unknown ids', () => {
    const h = host()
    expect(() => mkSelection(h.d, { region: h.d.root, regions: [], nodes: [h.nB], wires: [] }))
      .toThrowError(/node 'n1' is not directly in selection region/)
    expect(() => mkSelection(h.d, { region: h.d.root, regions: [h.cut, h.cut], nodes: [], wires: [] }))
      .toThrowError(/duplicate selected region 'r1'/)
    expect(() => mkSelection(h.d, { region: h.d.root, regions: [], nodes: ['ghost'], wires: [] }))
      .toThrowError(/unknown node 'ghost'/)
  })

  it('rejects explicit wires not scoped at the region or with unselected endpoints', () => {
    const h = host()
    // wShared has an endpoint on nB (inside the cut) — selecting it without the cut fails
    expect(() => mkSelection(h.d, { region: h.d.root, regions: [], nodes: [h.nA], wires: [h.wShared] }))
      .toThrowError(/wire 'w0' has endpoints outside the selection/)
    // wBare is scoped inside the cut, not at the selection region
    expect(() => mkSelection(h.d, { region: h.d.root, regions: [], nodes: [h.nA], wires: [h.wBare] }))
      .toThrowError(/wire 'w1' is not scoped at selection region/)
  })
})

describe('selectionContents', () => {
  it('classifies wires: scoped-inside-subtree internal, cross-boundary touching', () => {
    const h = host()
    // select ONLY the cut subtree: nB inside, wShared touches nB from outside
    const sel = mkSelection(h.d, { region: h.d.root, regions: [h.cut], nodes: [], wires: [] })
    const c = selectionContents(h.d, sel)
    expect([...c.allRegions]).toEqual([h.cut])
    expect([...c.allNodes]).toEqual([h.nB])
    expect(c.internalWires).toContain(h.wBare) // scoped inside the selected cut
    expect(c.touchingWires).toContain(h.wShared) // endpoint on nB, scope outside
  })

  it('explicitly selected top-level wires are internal; unselected all-inside wires are touching', () => {
    const h = host()
    const withWire = mkSelection(h.d, {
      region: h.d.root, regions: [h.cut], nodes: [h.nA], wires: [h.wShared],
    })
    expect(selectionContents(h.d, withWire).internalWires).toContain(h.wShared)

    const withoutWire = mkSelection(h.d, {
      region: h.d.root, regions: [h.cut], nodes: [h.nA], wires: [],
    })
    // all endpoints selected, but membership is the caller's choice
    expect(selectionContents(h.d, withoutWire).touchingWires).toContain(h.wShared)
  })

  it('wires with no contact are neither internal nor touching', () => {
    const h = host()
    const sel = mkSelection(h.d, { region: h.d.root, regions: [], nodes: [h.nA], wires: [] })
    const c = selectionContents(h.d, sel)
    expect(c.internalWires).not.toContain(h.wBare)
    expect(c.touchingWires).not.toContain(h.wBare)
  })

  it('zero-endpoint wires at the selection region are explicitly selectable and classify internal', () => {
    const b = new DiagramBuilder()
    const nA = b.termNode(b.root, p('\\x. x'))
    void nA
    const wEmpty = b.wire(b.root, [])
    const d = b.build()
    const sel = mkSelection(d, { region: d.root, regions: [], nodes: [], wires: [wEmpty] })
    expect(selectionContents(d, sel).internalWires).toContain(wEmpty)
  })
})
