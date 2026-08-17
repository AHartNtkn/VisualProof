import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { relSig, IOTA } from '../../src/kernel/diagram/sig'
import { diagramSpec } from '../../src/view3d/spec'

/** sheet: atom P(x); cut c1 containing atom Q(x) (same wire x crosses into c1);
    c1 contains empty cut c2. */
function fixture() {
  const b = new DiagramBuilder()
  const c1 = b.cut(b.root)
  const c2 = b.cut(c1)
  const P = b.atom(b.root, relSig([IOTA]))
  const Q = b.atom(c1, relSig([IOTA]))
  const x = b.wire([
    { node: P, port: { kind: 'arg', index: 0 } },
    { node: Q, port: { kind: 'arg', index: 0 } },
  ])
  return { d: b.build(), c1, c2, P, Q, x }
}

describe('diagramSpec', () => {
  it('lists every region, node, and wire exactly once with parents', () => {
    const { d, c1, c2, P, Q } = fixture()
    const s = diagramSpec(d)
    expect([...s.regions.keys()].sort()).toEqual(['r0', c1, c2].sort())
    expect(s.regions.get(c1)!.parent).toBe('r0')
    expect(s.regions.get(c2)!.parent).toBe(c1)
    expect(s.regions.get('r0')!.parent).toBeNull()
    const nodeIds = [...s.nodes.keys()]
    expect(nodeIds).toContain(P)
    expect(nodeIds).toContain(Q)
    // every wire's terminals reference existing nodes
    for (const w of s.wires) for (const t of w.terminals) expect(s.nodes.has(t.node)).toBe(true)
  })
  it('orders items: own nodes first (record order), then child branches', () => {
    const { d, c1, P } = fixture()
    const s = diagramSpec(d)
    const rootItems = s.regions.get('r0')!.items
    expect(rootItems[0]).toEqual({ kind: 'node', id: P })
    expect(rootItems[rootItems.length - 1]).toEqual({ kind: 'branch', region: c1 })
    const c1Items = s.regions.get(c1)!.items
    expect(c1Items.some((i) => i.kind === 'branch')).toBe(true)
  })
  it('atom port keys are head then args; ref args only', () => {
    const { d, P } = fixture()
    const s = diagramSpec(d)
    expect(s.nodes.get(P)!.portKeys).toEqual(['hd', 'a:0'])
  })
  it('escape counts: the P–Q wire crosses c1 but not c2', () => {
    const { d, c1, c2 } = fixture()
    const s = diagramSpec(d)
    expect(s.escapes.get(c1)).toBe(1)
    expect(s.escapes.get(c2)).toBe(0)
    expect(s.escapes.get('r0')).toBe(0)
  })
})
