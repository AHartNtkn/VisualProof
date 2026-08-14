import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
import { findOccurrences } from '../../../src/kernel/diagram/subgraph/match'
import { bareWire } from '../../fixtures/pins'

describe('open signature-indexed matching', () => {
  it('rejects a relational boundary attachment of a different signature', () => {
    const unary = relSig([IOTA])
    const nullary = relSig([])
    const patternBuilder = new DiagramBuilder()
    const boundary = patternBuilder.relWire(unary)
    const pattern = patternBuilder.buildOpen([boundary])

    const hostBuilder = new DiagramBuilder()
    const good = bareWire(hostBuilder, hostBuilder.root, unary)
    const bad = bareWire(hostBuilder, hostBuilder.root, nullary)
    const host = hostBuilder.build()

    // Exposed once, the pattern's line ends in one point; the host's bare line
    // has two, so the point embeds either way. Both are real occurrences and
    // they differ in exactly that image.
    const found = findOccurrences(host, pattern, { attachments: [good] }).matches
    expect(found).toHaveLength(2)
    const patternPoint = Object.keys(pattern.diagram.nodes)[0]!
    expect(found.map((match) => match.nodeMap.get(patternPoint)))
      .toEqual(host.wires[good]!.endpoints.map((end) => end.node))

    expect(findOccurrences(host, pattern, { attachments: [bad] }).matches)
      .toHaveLength(0)
  })

  it('rejects a seeded bare boundary wire whose signature does not match its attachment', () => {
    // A wire with zero real endpoints and no node content anywhere has no
    // endpoint-based signal for the search to catch a signature mismatch
    // through: the wire's own sig is the ONLY thing that can distinguish a
    // wrong-signature seed. It needs the two-end floor, so — like the
    // twice-exposed fixture in match.test.ts — it is exposed at two
    // boundary positions with no real endpoints of its own.
    const patternBuilder = mkDiagramWithBoundary({
      root: 'p0',
      regions: { p0: { kind: 'sheet' } },
      nodes: {},
      wires: { stub: { sig: IOTA, endpoints: [] } },
    }, ['stub', 'stub'])

    const hostBuilder = new DiagramBuilder()
    const matching = bareWire(hostBuilder, hostBuilder.root, IOTA)
    const mismatched = bareWire(hostBuilder, hostBuilder.root, relSig([]))
    const host = hostBuilder.build()

    const good = findOccurrences(host, patternBuilder, { attachments: [matching, matching] })
    expect(good.status).toBe('complete')
    expect(good.matches).toHaveLength(1)

    const bad = findOccurrences(host, patternBuilder, { attachments: [mismatched, mismatched] })
    expect(bad.status).toBe('complete')
    expect(bad.matches).toEqual([])
  })

  it('matches an endpointful atom-head stub only to an equal-signature line', () => {
    const unary = relSig([IOTA])
    const binary = relSig([IOTA, IOTA])
    const patternBuilder = new DiagramBuilder()
    const patternAtom = patternBuilder.atom(patternBuilder.root, unary)
    const boundary = patternBuilder.wire(
      [{ node: patternAtom, port: { kind: 'head' } }],
      unary,
    )
    const pattern = patternBuilder.buildOpen([boundary])

    const hostBuilder = new DiagramBuilder()
    const goodAtom = hostBuilder.atom(hostBuilder.root, unary)
    const good = hostBuilder.wire(
      [{ node: goodAtom, port: { kind: 'head' } }],
      unary,
    )
    const badAtom = hostBuilder.atom(hostBuilder.root, binary)
    const bad = hostBuilder.wire(
      [{ node: badAtom, port: { kind: 'head' } }],
      binary,
    )
    const host = hostBuilder.build()

    expect(findOccurrences(host, pattern, { attachments: [good] }).matches)
      .toHaveLength(1)
    expect(findOccurrences(host, pattern, { attachments: [bad] }).matches)
      .toHaveLength(0)
  })

  it('preserves sharing of two atom heads on one relational line', () => {
    const relation = relSig([])
    const patternBuilder = new DiagramBuilder()
    const firstPatternAtom = patternBuilder.atom(patternBuilder.root, relation)
    const secondPatternAtom = patternBuilder.atom(patternBuilder.root, relation)
    patternBuilder.wire([
      { node: firstPatternAtom, port: { kind: 'head' } },
      { node: secondPatternAtom, port: { kind: 'head' } },
    ], relation)
    const pattern = patternBuilder.buildOpen([])

    const sharedBuilder = new DiagramBuilder()
    const firstSharedAtom = sharedBuilder.atom(sharedBuilder.root, relation)
    const secondSharedAtom = sharedBuilder.atom(sharedBuilder.root, relation)
    sharedBuilder.wire([
      { node: firstSharedAtom, port: { kind: 'head' } },
      { node: secondSharedAtom, port: { kind: 'head' } },
    ], relation)

    const separateBuilder = new DiagramBuilder()
    separateBuilder.atom(separateBuilder.root, relation)
    separateBuilder.atom(separateBuilder.root, relation)

    expect(findOccurrences(sharedBuilder.build(), pattern).matches).toHaveLength(1)
    expect(findOccurrences(separateBuilder.build(), pattern).matches).toHaveLength(0)
  })
})
