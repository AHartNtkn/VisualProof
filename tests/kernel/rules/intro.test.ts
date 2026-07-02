import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { termEq } from '../../../src/kernel/term/term'
import type { Diagram, NodeId } from '../../../src/kernel/diagram/diagram'
import { DiagramError } from '../../../src/kernel/diagram/diagram'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { diagramFingerprint } from '../../../src/kernel/diagram/canonical/fingerprint'
import { applyClosedTermIntro } from '../../../src/kernel/rules/intro'
import { applyInsertion } from '../../../src/kernel/rules/insertion'
import { RuleError } from '../../../src/kernel/rules/error'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

/** The single term node present in `out` but not in `before`. */
function newNode(out: Diagram, before: Diagram): NodeId {
  const added = Object.keys(out.nodes).filter((id) => before.nodes[id] === undefined)
  expect(added).toHaveLength(1)
  return added[0]!
}

describe('closed-term introduction', () => {
  it('introduces a closed term at root (positive): one node, one fresh singleton output wire, nothing else', () => {
    const h = new DiagramBuilder()
    const bystander = h.termNode(h.root, p('\\x. x q'))
    const d = h.build()
    const t = p('\\x. \\y. x')
    const out = applyClosedTermIntro(d, d.root, t)

    const made = newNode(out, d)
    const n = out.nodes[made]!
    expect(n.kind === 'term' && n.region === d.root && termEq(n.term, t)).toBe(true)

    // exactly one new wire: the made node's output, a fresh singleton scoped at the region
    const addedWires = Object.entries(out.wires).filter(([id]) => d.wires[id] === undefined)
    expect(addedWires).toHaveLength(1)
    const [, w] = addedWires[0]!
    expect(w.scope).toBe(d.root)
    expect(w.endpoints).toEqual([{ node: made, port: { kind: 'output' } }])

    // nothing else changed: regions identical, prior nodes and wires untouched
    expect(out.regions).toEqual(d.regions)
    expect(Object.keys(out.nodes)).toHaveLength(Object.keys(d.nodes).length + 1)
    expect(Object.keys(out.wires)).toHaveLength(Object.keys(d.wires).length + 1)
    expect(out.nodes[bystander]).toEqual(d.nodes[bystander])
    for (const [id, wv] of Object.entries(d.wires)) expect(out.wires[id]).toEqual(wv)
  })

  it('introduces inside a cut (negative region) — no polarity gate; wire scoped at the cut', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const d = h.build()
    const t = p('\\x. \\y. y')
    const out = applyClosedTermIntro(d, cut, t)
    const made = newNode(out, d)
    const n = out.nodes[made]!
    expect(n.kind === 'term' && n.region === cut && termEq(n.term, t)).toBe(true)
    const addedWires = Object.entries(out.wires).filter(([id]) => d.wires[id] === undefined)
    expect(addedWires).toHaveLength(1)
    expect(addedWires[0]![1].scope).toBe(cut)
    expect(addedWires[0]![1].endpoints).toHaveLength(1)
  })

  it('introduces inside a bubble; wire scoped at the bubble', () => {
    const h = new DiagramBuilder()
    const bub = h.bubble(h.root, 1)
    const a = h.atom(bub, bub)
    h.wire(bub, [{ node: a, port: { kind: 'arg', index: 0 } }])
    const d = h.build()
    const t = p('\\x. x')
    const out = applyClosedTermIntro(d, bub, t)
    const made = newNode(out, d)
    const n = out.nodes[made]!
    expect(n.kind === 'term' && n.region === bub && termEq(n.term, t)).toBe(true)
    const addedWires = Object.entries(out.wires).filter(([id]) => d.wires[id] === undefined)
    expect(addedWires).toHaveLength(1)
    expect(addedWires[0]![1].scope).toBe(bub)
  })

  it('refuses an open term, naming the closed-term gate and the offending free ports', () => {
    const d = new DiagramBuilder().build()
    expect(() => applyClosedTermIntro(d, d.root, p('\\x. x q'))).toThrowError(RuleError)
    expect(() => applyClosedTermIntro(d, d.root, p('f (\\x. x q)')))
      .toThrowError(/closed-term introduction requires a closed term.*'f'.*'q'/)
  })

  it('is subsumed by insertion in a negative region: applyInsertion draws the identical shape', () => {
    // The rule header's negative-region validity argument claims insertion
    // could already draw this node+wire shape there. Observe it: an
    // empty-boundary pattern of one term node on a singleton output wire,
    // inserted into a cut, is fingerprint-identical to closedTermIntro.
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const d = h.build()
    const t = p('\\x. \\y. x')
    const b = new DiagramBuilder()
    const n = b.termNode(b.root, t)
    b.wire(b.root, [{ node: n, port: { kind: 'output' } }])
    const pattern = mkDiagramWithBoundary(b.build(), [])
    const viaInsertion = applyInsertion(d, cut, pattern, [])
    const viaIntro = applyClosedTermIntro(d, cut, t)
    expect(diagramFingerprint(viaInsertion)).toBe(diagramFingerprint(viaIntro))
  })

  it('rejects an unknown region structurally', () => {
    const d = new DiagramBuilder().build()
    expect(() => applyClosedTermIntro(d, 'ghost', p('\\x. x'))).toThrowError(DiagramError)
    expect(() => applyClosedTermIntro(d, 'ghost', p('\\x. x'))).toThrowError(/unknown region 'ghost'/)
  })
})
