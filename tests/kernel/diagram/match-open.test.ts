import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
import { findOccurrences } from '../../../src/kernel/diagram/subgraph/match'

describe('open signature-indexed matching', () => {
  it('rejects a relational boundary attachment of a different signature', () => {
    const unary = relSig([IOTA])
    const nullary = relSig([])
    const patternBuilder = new DiagramBuilder()
    const boundary = patternBuilder.relWire(patternBuilder.root, unary)
    const pattern = mkDiagramWithBoundary(patternBuilder.build(), [boundary])

    const hostBuilder = new DiagramBuilder()
    const good = hostBuilder.relWire(hostBuilder.root, unary)
    const bad = hostBuilder.relWire(hostBuilder.root, nullary)
    const host = hostBuilder.build()

    expect(findOccurrences(host, pattern, { attachments: [good] }).matches)
      .toHaveLength(1)
    expect(findOccurrences(host, pattern, { attachments: [bad] }).matches)
      .toHaveLength(0)
  })

  it('matches an endpointful atom-head stub only to an equal-signature line', () => {
    const unary = relSig([IOTA])
    const binary = relSig([IOTA, IOTA])
    const patternBuilder = new DiagramBuilder()
    const patternAtom = patternBuilder.atom(patternBuilder.root, unary)
    const boundary = patternBuilder.wire(
      patternBuilder.root,
      [{ node: patternAtom, port: { kind: 'head' } }],
      unary,
    )
    const pattern = mkDiagramWithBoundary(patternBuilder.build(), [boundary])

    const hostBuilder = new DiagramBuilder()
    const goodAtom = hostBuilder.atom(hostBuilder.root, unary)
    const good = hostBuilder.wire(
      hostBuilder.root,
      [{ node: goodAtom, port: { kind: 'head' } }],
      unary,
    )
    const badAtom = hostBuilder.atom(hostBuilder.root, binary)
    const bad = hostBuilder.wire(
      hostBuilder.root,
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
    patternBuilder.wire(patternBuilder.root, [
      { node: firstPatternAtom, port: { kind: 'head' } },
      { node: secondPatternAtom, port: { kind: 'head' } },
    ], relation)
    const pattern = mkDiagramWithBoundary(patternBuilder.build(), [])

    const sharedBuilder = new DiagramBuilder()
    const firstSharedAtom = sharedBuilder.atom(sharedBuilder.root, relation)
    const secondSharedAtom = sharedBuilder.atom(sharedBuilder.root, relation)
    sharedBuilder.wire(sharedBuilder.root, [
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
