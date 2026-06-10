import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { findOccurrences } from '../../../src/kernel/diagram/subgraph/match'
import { occurrenceToSelection } from '../../../src/kernel/diagram/subgraph/occurrence'
import { removeSubgraph } from '../../../src/kernel/diagram/subgraph/splice'
import { selectionContents } from '../../../src/kernel/diagram/subgraph/selection'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

describe('occurrenceToSelection', () => {
  it('converts a mixed occurrence (root node + subtree + internal root wire) to a valid selection', () => {
    // pattern: node `y x` at root, a cut holding `\x. y x`, an explicit internal
    // root-scoped wire joining their y-ports, and the v:x wire as boundary
    const b = new DiagramBuilder()
    const nA = b.termNode(b.root, p('y x'))
    const cut = b.cut(b.root)
    const nB = b.termNode(cut, p('\\x. y x'))
    b.wire(b.root, [
      { node: nA, port: { kind: 'freeVar', name: 'y' } },
      { node: nB, port: { kind: 'freeVar', name: 'y' } },
    ])
    const stub = b.wire(b.root, [{ node: nA, port: { kind: 'freeVar', name: 'x' } }])
    const pattern = mkDiagramWithBoundary(b.build(), [stub])

    // host: an exact copy of the pattern content, plus an external node wired
    // to the attachment
    const h = new DiagramBuilder()
    const hA = h.termNode(h.root, p('y x'))
    const hcut = h.cut(h.root)
    const hB = h.termNode(hcut, p('\\x. y x'))
    h.wire(h.root, [
      { node: hA, port: { kind: 'freeVar', name: 'y' } },
      { node: hB, port: { kind: 'freeVar', name: 'y' } },
    ])
    const ext = h.termNode(h.root, p('\\x. x'))
    h.wire(h.root, [
      { node: hA, port: { kind: 'freeVar', name: 'x' } },
      { node: ext, port: { kind: 'output' } },
    ])
    const host = h.build()

    const r = findOccurrences(host, pattern, { fuel: 100 })
    expect(r.matches).toHaveLength(1)
    const sel = occurrenceToSelection(host, pattern, r.matches[0]!)
    expect(sel.region).toBe(host.root)
    expect(sel.nodes).toContain(hA)
    expect(sel.regions).toContain(hcut)
    const c = selectionContents(host, sel)
    expect(c.allNodes.has(hB)).toBe(true)
  })

  it('never selects attachment wires: removal trims them instead of deleting (the trap)', () => {
    // pattern: single node `y` with its v:y wire as boundary
    const b = new DiagramBuilder()
    const n = b.termNode(b.root, p('y'))
    const stub = b.wire(b.root, [{ node: n, port: { kind: 'freeVar', name: 'y' } }])
    const pattern = mkDiagramWithBoundary(b.build(), [stub])

    // host: the attachment wire's ONLY endpoint is inside the occurrence —
    // the dangerous case where naive conversion would select and delete it
    const h = new DiagramBuilder()
    const hn = h.termNode(h.root, p('y'))
    const hw = h.wire(h.root, [{ node: hn, port: { kind: 'freeVar', name: 'y' } }])
    const host = h.build()

    const r = findOccurrences(host, pattern, { fuel: 100 })
    expect(r.matches).toHaveLength(1)
    expect(r.matches[0]?.attachments).toEqual([hw])
    const sel = occurrenceToSelection(host, pattern, r.matches[0]!)
    expect(sel.wires).not.toContain(hw)
    const after = removeSubgraph(host, sel)
    // the attachment survives as a bare wire — trimmed, not deleted
    expect(after.wires[hw]).toBeDefined()
    expect(after.wires[hw]?.endpoints).toHaveLength(0)
  })

  it('throws loudly when the occurrence is missing an image', () => {
    const b = new DiagramBuilder()
    b.termNode(b.root, p('\\x. x'))
    const pattern = mkDiagramWithBoundary(b.build(), [])
    const h = new DiagramBuilder()
    h.termNode(h.root, p('\\x. x'))
    const host = h.build()
    const r = findOccurrences(host, pattern, { fuel: 100 })
    const broken = { ...r.matches[0]!, nodeMap: new Map<string, string>() }
    expect(() => occurrenceToSelection(host, pattern, broken))
      .toThrowError(/occurrence is missing an image for pattern node 'n0'/)
  })
})
