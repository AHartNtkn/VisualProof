import { describe, it, expect } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { extractSubgraph } from '../../../src/kernel/diagram/subgraph/extract'
import { spliceSubgraph } from '../../../src/kernel/diagram/subgraph/splice'
import { IOTA, relSig, sigEquals } from '../../../src/kernel/diagram/sig'
import { bareWire } from '../../fixtures/pins'

const head = { kind: 'head' as const }

/**
 * Wire-model counterpart of the deleted binder-map splice suite. There is no
 * binder map; reattaching a relational boundary stub is gated by signature
 * equality between the stub's line and the host line it lands on.
 */
describe('splice signature gate', () => {
  it('lands a relational boundary stub onto an equal-sig host line', () => {
    const S = relSig([IOTA])
    const pb = new DiagramBuilder()
    const a = pb.atom(pb.root, S)
    const stub = pb.wire([{ node: a, port: head }], S)
    const pattern = pb.buildOpen([stub])

    const hb = new DiagramBuilder()
    const hostRel = bareWire(hb, hb.root, S) // an existential relation line of sig S
    const host = hb.build()

    const out = spliceSubgraph(host, host.root, pattern, [hostRel])
    const landed = out.wires[hostRel]!
    expect(sigEquals(landed.sig, S)).toBe(true)
    expect(landed.endpoints.some((ep) => ep.port.kind === 'head')).toBe(true)
  })

  it('refuses to land a relational stub on a host line of a different sig, naming both sigs', () => {
    const S = relSig([IOTA])
    const T = relSig([])
    const pb = new DiagramBuilder()
    const a = pb.atom(pb.root, S)
    const stub = pb.wire([{ node: a, port: head }], S)
    const pattern = pb.buildOpen([stub])

    const hb = new DiagramBuilder()
    const hostBad = bareWire(hb, hb.root, T)
    const host = hb.build()

    expect(() => spliceSubgraph(host, host.root, pattern, [hostBad]))
      .toThrowError(/cannot land on attachment wire.*sig/)
    // both signatures appear in the message
    try {
      spliceSubgraph(host, host.root, pattern, [hostBad])
      throw new Error('expected the sig gate to reject')
    } catch (e) {
      const msg = e instanceof Error ? e.message : String(e)
      expect(msg).toContain('(i)') // sig of T = rel([]) → sigKey '()' ; sig of S = rel([i]) → '(i)'
      expect(msg).toContain('()')
    }
  })

  it('extract → splice round-trips a relational stub onto its equal-sig source line', () => {
    // ∃R at the root; R(...) inside a cut. Extract the cut and splice a second
    // copy back at the root onto the SAME relation line — equal sig, accepted.
    const S = relSig([IOTA])
    const b = new DiagramBuilder()
    const cut = b.cut(b.root)
    const a = b.atom(cut, S)
    const headWire = b.wire([{ node: a, port: head }], S)
    // ∃R lives at the root, above the cut holding its application.
    b.pin(headWire, b.root)
    const d = b.build()
    const sel = mkSelection(d, { region: d.root, regions: [cut], nodes: [], wires: [] })
    const ex = extractSubgraph(d, sel)
    expect(ex.attachments).toEqual([headWire])

    const out = spliceSubgraph(d, d.root, ex.pattern, ex.attachments)
    // the relation line now carries the original atom head plus the copy's head
    const heads = out.wires[headWire]!.endpoints.filter((ep) => ep.port.kind === 'head')
    expect(heads).toHaveLength(2)
  })
})
