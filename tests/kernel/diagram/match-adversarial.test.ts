import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
import { findOccurrences } from '../../../src/kernel/diagram/subgraph/match'

describe('exact occurrence matching adversarial battery', () => {
  it('matches exact reference content with positional wiring intact', () => {
    const patternBuilder = new DiagramBuilder()
    const patternRef = patternBuilder.ref(
      patternBuilder.root,
      'P',
      relSig([IOTA, IOTA]),
    )
    const firstStub = patternBuilder.wire(patternBuilder.root, [
      { node: patternRef, port: { kind: 'arg', index: 0 } },
    ])
    const secondStub = patternBuilder.wire(patternBuilder.root, [
      { node: patternRef, port: { kind: 'arg', index: 1 } },
    ])
    const pattern = mkDiagramWithBoundary(
      patternBuilder.build(),
      [firstStub, secondStub],
    )

    const hostBuilder = new DiagramBuilder()
    const hostRef = hostBuilder.ref(
      hostBuilder.root,
      'P',
      relSig([IOTA, IOTA]),
    )
    const firstWire = hostBuilder.wire(hostBuilder.root, [
      { node: hostRef, port: { kind: 'arg', index: 0 } },
    ])
    const secondWire = hostBuilder.wire(hostBuilder.root, [
      { node: hostRef, port: { kind: 'arg', index: 1 } },
    ])
    const host = hostBuilder.build()

    expect(findOccurrences(host, pattern, {
      attachments: [firstWire, secondWire],
    }).matches).toHaveLength(1)
    expect(findOccurrences(host, pattern, {
      attachments: [secondWire, firstWire],
    }).matches).toHaveLength(0)
  })

  it('returns only exact graph-search fields and no semantic verdict channel', () => {
    const patternBuilder = new DiagramBuilder()
    patternBuilder.ref(patternBuilder.root, 'P', relSig([]))
    const pattern = mkDiagramWithBoundary(patternBuilder.build(), [])
    const hostBuilder = new DiagramBuilder()
    hostBuilder.ref(hostBuilder.root, 'P', relSig([]))
    const result = findOccurrences(hostBuilder.build(), pattern)

    expect(result.matches).toHaveLength(1)
    expect(Object.keys(result).sort()).toEqual([
      'explorationSteps',
      'matches',
      'status',
    ])
  })

  it('deduplicates symmetric interior bijections by footprint', () => {
    const patternBuilder = new DiagramBuilder()
    patternBuilder.ref(patternBuilder.root, 'P', relSig([]))
    patternBuilder.ref(patternBuilder.root, 'P', relSig([]))
    const pattern = mkDiagramWithBoundary(patternBuilder.build(), [])
    const hostBuilder = new DiagramBuilder()
    hostBuilder.ref(hostBuilder.root, 'P', relSig([]))
    hostBuilder.ref(hostBuilder.root, 'P', relSig([]))

    expect(findOccurrences(hostBuilder.build(), pattern).matches).toHaveLength(1)
  })

  it('retains distinct partial-selection footprints', () => {
    const patternBuilder = new DiagramBuilder()
    patternBuilder.ref(patternBuilder.root, 'P', relSig([]))
    const pattern = mkDiagramWithBoundary(patternBuilder.build(), [])
    const hostBuilder = new DiagramBuilder()
    hostBuilder.ref(hostBuilder.root, 'P', relSig([]))
    hostBuilder.ref(hostBuilder.root, 'P', relSig([]))

    expect(findOccurrences(hostBuilder.build(), pattern).matches).toHaveLength(2)
  })

  it('uses exact wire sets below the root and subset semantics at the root', () => {
    const nestedPatternBuilder = new DiagramBuilder()
    const patternCut = nestedPatternBuilder.cut(nestedPatternBuilder.root)
    nestedPatternBuilder.wire(patternCut, [])
    const nestedPattern = mkDiagramWithBoundary(
      nestedPatternBuilder.build(),
      [],
    )

    const nestedHostBuilder = new DiagramBuilder()
    const hostCut = nestedHostBuilder.cut(nestedHostBuilder.root)
    nestedHostBuilder.wire(hostCut, [])
    nestedHostBuilder.wire(hostCut, [])
    expect(findOccurrences(nestedHostBuilder.build(), nestedPattern).matches)
      .toHaveLength(0)

    const rootPatternBuilder = new DiagramBuilder()
    rootPatternBuilder.wire(rootPatternBuilder.root, [])
    const rootPattern = mkDiagramWithBoundary(rootPatternBuilder.build(), [])
    const rootHostBuilder = new DiagramBuilder()
    rootHostBuilder.wire(rootHostBuilder.root, [])
    rootHostBuilder.wire(rootHostBuilder.root, [])
    expect(findOccurrences(
      rootHostBuilder.build(),
      rootPattern,
      { inRegion: rootHostBuilder.root },
    ).matches).toHaveLength(2)
  })

  it('rejects an internal wire whose host scope differs', () => {
    const patternBuilder = new DiagramBuilder()
    const patternCut = patternBuilder.cut(patternBuilder.root)
    const patternRef = patternBuilder.ref(
      patternCut,
      'P',
      relSig([IOTA]),
    )
    patternBuilder.wire(patternCut, [
      { node: patternRef, port: { kind: 'arg', index: 0 } },
    ])
    const pattern = mkDiagramWithBoundary(patternBuilder.build(), [])

    const hostBuilder = new DiagramBuilder()
    const hostCut = hostBuilder.cut(hostBuilder.root)
    const hostRef = hostBuilder.ref(hostCut, 'P', relSig([IOTA]))
    hostBuilder.wire(hostBuilder.root, [
      { node: hostRef, port: { kind: 'arg', index: 0 } },
    ])

    expect(findOccurrences(hostBuilder.build(), pattern).matches).toHaveLength(0)
  })

  it('rejects a scope swap that preserves per-region wire counts', () => {
    const patternBuilder = new DiagramBuilder()
    const patternCut = patternBuilder.cut(patternBuilder.root)
    const patternA = patternBuilder.ref(patternCut, 'A', relSig([IOTA]))
    const patternB = patternBuilder.ref(patternCut, 'B', relSig([IOTA]))
    patternBuilder.wire(patternCut, [
      { node: patternA, port: { kind: 'arg', index: 0 } },
    ])
    patternBuilder.wire(patternBuilder.root, [
      { node: patternB, port: { kind: 'arg', index: 0 } },
    ])
    const pattern = mkDiagramWithBoundary(patternBuilder.build(), [])

    const hostBuilder = new DiagramBuilder()
    const hostCut = hostBuilder.cut(hostBuilder.root)
    const hostA = hostBuilder.ref(hostCut, 'A', relSig([IOTA]))
    const hostB = hostBuilder.ref(hostCut, 'B', relSig([IOTA]))
    hostBuilder.wire(hostBuilder.root, [
      { node: hostA, port: { kind: 'arg', index: 0 } },
    ])
    hostBuilder.wire(hostCut, [
      { node: hostB, port: { kind: 'arg', index: 0 } },
    ])

    expect(findOccurrences(hostBuilder.build(), pattern).matches).toHaveLength(0)
  })

  it('requires a multi-endpoint boundary stub to land on one containing wire', () => {
    const patternBuilder = new DiagramBuilder()
    const first = patternBuilder.ref(
      patternBuilder.root,
      'P',
      relSig([IOTA]),
    )
    const second = patternBuilder.ref(
      patternBuilder.root,
      'P',
      relSig([IOTA]),
    )
    const stub = patternBuilder.wire(patternBuilder.root, [
      { node: first, port: { kind: 'arg', index: 0 } },
      { node: second, port: { kind: 'arg', index: 0 } },
    ])
    const pattern = mkDiagramWithBoundary(patternBuilder.build(), [stub])

    const sharedBuilder = new DiagramBuilder()
    const sharedFirst = sharedBuilder.ref(
      sharedBuilder.root,
      'P',
      relSig([IOTA]),
    )
    const sharedSecond = sharedBuilder.ref(
      sharedBuilder.root,
      'P',
      relSig([IOTA]),
    )
    sharedBuilder.wire(sharedBuilder.root, [
      { node: sharedFirst, port: { kind: 'arg', index: 0 } },
      { node: sharedSecond, port: { kind: 'arg', index: 0 } },
    ])

    const separateBuilder = new DiagramBuilder()
    separateBuilder.ref(separateBuilder.root, 'P', relSig([IOTA]))
    separateBuilder.ref(separateBuilder.root, 'P', relSig([IOTA]))

    expect(findOccurrences(sharedBuilder.build(), pattern).matches).toHaveLength(1)
    expect(findOccurrences(separateBuilder.build(), pattern).matches).toHaveLength(0)
  })

  it('matches atoms exactly and respects relation arity', () => {
    const pattern = (arity: number) => {
      const builder = new DiagramBuilder()
      builder.atom(
        builder.root,
        relSig(Array.from({ length: arity }, () => IOTA)),
      )
      return mkDiagramWithBoundary(builder.build(), [])
    }
    const hostBuilder = new DiagramBuilder()
    hostBuilder.atom(hostBuilder.root, relSig([IOTA]))
    const host = hostBuilder.build()

    expect(findOccurrences(host, pattern(1)).matches).toHaveLength(1)
    expect(findOccurrences(host, pattern(2)).matches).toHaveLength(0)
  })
})
