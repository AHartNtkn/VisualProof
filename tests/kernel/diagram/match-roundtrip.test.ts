import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary, type DiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { spliceSubgraph } from '../../../src/kernel/diagram/subgraph/splice'
import { findOccurrences } from '../../../src/kernel/diagram/subgraph/match'
import type { Diagram, RegionId, WireId } from '../../../src/kernel/diagram/diagram'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

function expectFound(
  host: Diagram,
  at: RegionId,
  pattern: DiagramWithBoundary,
  attachments: readonly WireId[],
): void {
  const spliced = spliceSubgraph(host, at, pattern, attachments)
  const r = findOccurrences(spliced, pattern, { fuel: 200 })
  const hit = r.matches.find(
    (m) => m.region === at && JSON.stringify(m.attachments) === JSON.stringify(attachments),
  )
  expect(hit, `expected an occurrence at '${at}' with attachments ${JSON.stringify(attachments)}`).toBeDefined()
}

describe('splice → match round-trip', () => {
  it('finds a spliced node pattern at the root with its attachment', () => {
    const b = new DiagramBuilder()
    const n = b.termNode(b.root, p('y x'))
    const stub = b.wire(b.root, [{ node: n, port: { kind: 'freeVar', name: 'y' } }])
    const pattern = mkDiagramWithBoundary(b.build(), [stub])

    const h = new DiagramBuilder()
    const hn = h.termNode(h.root, p('\\x. x'))
    const hw = h.wire(h.root, [{ node: hn, port: { kind: 'output' } }])
    expectFound(h.build(), 'r0', pattern, [hw])
  })

  it('finds a spliced pattern deep inside nested cuts (the iteration shape)', () => {
    const b = new DiagramBuilder()
    const n = b.termNode(b.root, p('y'))
    const stub = b.wire(b.root, [{ node: n, port: { kind: 'freeVar', name: 'y' } }])
    const pattern = mkDiagramWithBoundary(b.build(), [stub])

    const h = new DiagramBuilder()
    const outer = h.cut(h.root)
    const inner = h.cut(outer)
    const hn = h.termNode(h.root, p('\\x. x'))
    const hw = h.wire(h.root, [{ node: hn, port: { kind: 'output' } }])
    const host = h.build()
    expectFound(host, inner, pattern, [hw])
  })

  it('finds a spliced cut-subtree pattern with a crossing boundary', () => {
    const b = new DiagramBuilder()
    const cut = b.cut(b.root)
    const n = b.termNode(cut, p('\\x. y x'))
    const stub = b.wire(b.root, [{ node: n, port: { kind: 'freeVar', name: 'y' } }])
    const pattern = mkDiagramWithBoundary(b.build(), [stub])

    const h = new DiagramBuilder()
    const hn = h.termNode(h.root, p('\\x. x'))
    const hw = h.wire(h.root, [{ node: hn, port: { kind: 'output' } }])
    expectFound(h.build(), 'r0', pattern, [hw])
  })

  it('finds a bubble-with-atom pattern after splicing', () => {
    const b = new DiagramBuilder()
    const bub = b.bubble(b.root, 1)
    const a = b.atom(bub, bub)
    const t = b.termNode(bub, p('\\x. x'))
    b.wire(bub, [
      { node: t, port: { kind: 'output' } },
      { node: a, port: { kind: 'arg', index: 0 } },
    ])
    const pattern = mkDiagramWithBoundary(b.build(), [])

    const h = new DiagramBuilder()
    h.termNode(h.root, p('\\x. \\y. x'))
    expectFound(h.build(), 'r0', pattern, [])
  })

  it('finds repeated-attachment splices (two stubs on one host wire)', () => {
    const b = new DiagramBuilder()
    const n = b.termNode(b.root, p('y x'))
    const sY = b.wire(b.root, [{ node: n, port: { kind: 'freeVar', name: 'y' } }])
    const sX = b.wire(b.root, [{ node: n, port: { kind: 'freeVar', name: 'x' } }])
    const pattern = mkDiagramWithBoundary(b.build(), [sY, sX])

    const h = new DiagramBuilder()
    const hn = h.termNode(h.root, p('\\x. x'))
    const hw = h.wire(h.root, [{ node: hn, port: { kind: 'output' } }])
    expectFound(h.build(), 'r0', pattern, [hw, hw])
  })

  it('attachment order is index-aligned with the boundary (distinct wires)', () => {
    const b = new DiagramBuilder()
    const n = b.termNode(b.root, p('y x'))
    const sY = b.wire(b.root, [{ node: n, port: { kind: 'freeVar', name: 'y' } }])
    const sX = b.wire(b.root, [{ node: n, port: { kind: 'freeVar', name: 'x' } }])
    const pattern = mkDiagramWithBoundary(b.build(), [sY, sX])

    const h = new DiagramBuilder()
    const n1 = h.termNode(h.root, p('\\x. x'))
    const n2 = h.termNode(h.root, p('\\x. \\y. x'))
    const hw1 = h.wire(h.root, [{ node: n1, port: { kind: 'output' } }])
    const hw2 = h.wire(h.root, [{ node: n2, port: { kind: 'output' } }])
    const host = h.build()
    // splice with [hw1, hw2]; the found occurrence must report exactly that order
    expectFound(host, 'r0', pattern, [hw1, hw2])
    // and the reversed splice must report the reversed order
    expectFound(host, 'r0', pattern, [hw2, hw1])
  })

  it('extract-elsewhere-splice yields at least two occurrences (deiteration shape)', () => {
    // host already contains the pattern once; splice a second copy into a cut:
    // the matcher must report both
    const b = new DiagramBuilder()
    const n = b.termNode(b.root, p('y'))
    const stub = b.wire(b.root, [{ node: n, port: { kind: 'freeVar', name: 'y' } }])
    const pattern = mkDiagramWithBoundary(b.build(), [stub])

    const h = new DiagramBuilder()
    const existing = h.termNode(h.root, p('y'))
    const hub = h.termNode(h.root, p('\\x. x'))
    const hw = h.wire(h.root, [
      { node: existing, port: { kind: 'freeVar', name: 'y' } },
      { node: hub, port: { kind: 'output' } },
    ])
    const cut = h.cut(h.root)
    const host = h.build()
    const spliced = spliceSubgraph(host, cut, pattern, [hw])
    const r = findOccurrences(spliced, pattern, { fuel: 100 })
    const regions = r.matches.map((m) => m.region).sort()
    expect(regions).toEqual([cut, host.root].sort())
    for (const m of r.matches) expect(m.attachments).toEqual([hw])
  })
})
