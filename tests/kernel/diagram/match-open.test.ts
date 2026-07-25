import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
import { findOccurrences } from '../../../src/kernel/diagram/subgraph/match'

const p = (s: string) => parseTerm(s)
const head = { kind: 'head' as const }

/**
 * Wire-model counterpart of the deleted open-binder matching suite. Binder
 * identity is gone; its role — which existential a relational port belongs to —
 * is now carried by which wire the port rides, and a corresponded pair of wires
 * must have equal signatures.
 */
describe('signature-gated wire correspondence', () => {
  it('refuses to correspond a relational boundary line to a host line of a different sig', () => {
    // Step-1 scenario: match refuses unequal-sig wire correspondence.
    const S = relSig([IOTA])
    const T = relSig([])
    const b = new DiagramBuilder()
    b.termNode(b.root, p('\\x. x'))
    const rel = b.relWire(b.root, S) // bare relational boundary line of sig S
    const pattern = mkDiagramWithBoundary(b.build(), [rel])

    const h = new DiagramBuilder()
    h.termNode(h.root, p('\\x. x'))
    const good = h.relWire(h.root, S)
    const bad = h.relWire(h.root, T)
    const host = h.build()

    // seeding the equal-sig line yields a match
    expect(findOccurrences(host, pattern, { fuel: 50, attachments: [good] }).matches).toHaveLength(1)
    // seeding the unequal-sig line is refused by the sig gate
    expect(findOccurrences(host, pattern, { fuel: 50, attachments: [bad] }).matches).toHaveLength(0)
  })

  it('an endpointful relational stub matches only an equal-sig host line', () => {
    // pattern: R(t) with R's head on a boundary stub of sig S; seed the host's
    // equal-sig relation line and refuse a wrong-sig one.
    const S = relSig([IOTA])
    const T = relSig([IOTA, IOTA])
    const pb = new DiagramBuilder()
    const pa = pb.atom(pb.root, S)
    const stub = pb.wire(pb.root, [{ node: pa, port: head }], S)
    const pattern = mkDiagramWithBoundary(pb.build(), [stub])

    const h = new DiagramBuilder()
    const ha = h.atom(h.root, S)
    const good = h.wire(h.root, [{ node: ha, port: head }], S)
    const hb2 = h.atom(h.root, T)
    const bad = h.wire(h.root, [{ node: hb2, port: head }], T)
    const host = h.build()

    expect(findOccurrences(host, pattern, { fuel: 50, attachments: [good] }).matches).toHaveLength(1)
    expect(findOccurrences(host, pattern, { fuel: 50, attachments: [bad] }).matches).toHaveLength(0)
  })

  it('two relational ports sharing one line match only a host that shares one line', () => {
    // Counterpart of "binder identity is exact": in the pattern two atoms ride
    // ONE relation line (the same existential). A host matches only when its two
    // atoms ride one shared line, not two separate ones.
    const S = relSig([])
    const pb = new DiagramBuilder()
    const pa1 = pb.atom(pb.root, S)
    const pa2 = pb.atom(pb.root, S)
    pb.wire(pb.root, [{ node: pa1, port: head }, { node: pa2, port: head }], S)
    const pattern = mkDiagramWithBoundary(pb.build(), [])

    const shared = (() => {
      const h = new DiagramBuilder()
      const a1 = h.atom(h.root, S)
      const a2 = h.atom(h.root, S)
      h.wire(h.root, [{ node: a1, port: head }, { node: a2, port: head }], S)
      return h.build()
    })()
    expect(findOccurrences(shared, pattern, { fuel: 50 }).matches).toHaveLength(1)

    const separate = (() => {
      const h = new DiagramBuilder()
      h.atom(h.root, S) // each head auto-wired onto its OWN line
      h.atom(h.root, S)
      return h.build()
    })()
    expect(findOccurrences(separate, pattern, { fuel: 50 }).matches).toHaveLength(0)
  })
})
