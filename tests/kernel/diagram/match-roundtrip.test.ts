import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import type { DiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import type {
  Diagram,
  RegionId,
  WireId,
} from '../../../src/kernel/diagram/diagram'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
import { findOccurrences } from '../../../src/kernel/diagram/subgraph/match'
import { spliceSubgraph } from '../../../src/kernel/diagram/subgraph/splice'
import { bareWire } from '../../fixtures/pins'

function expectFound(
  host: Diagram,
  atRegion: RegionId,
  pattern: DiagramWithBoundary,
  attachments: readonly WireId[],
): Diagram {
  const spliced = spliceSubgraph(host, atRegion, pattern, attachments)
  const result = findOccurrences(spliced, pattern)
  const occurrence = result.matches.find((candidate) =>
    candidate.region === atRegion
    && JSON.stringify(candidate.attachments) === JSON.stringify(attachments),
  )
  expect(
    occurrence,
    `expected occurrence at '${atRegion}' with ${JSON.stringify(attachments)}`,
  ).toBeDefined()
  return spliced
}

function unaryRefPattern(defId = 'P'): DiagramWithBoundary {
  const builder = new DiagramBuilder()
  const ref = builder.ref(builder.root, defId, relSig([IOTA]))
  const stub = builder.wire([
    { node: ref, port: { kind: 'arg', index: 0 } },
  ])
  return builder.buildOpen([stub])
}

describe('splice to exact-match round trip', () => {
  it('finds a spliced reference pattern at the root with its attachment', () => {
    const pattern = unaryRefPattern()
    const hostBuilder = new DiagramBuilder()
    const attachment = bareWire(hostBuilder, hostBuilder.root)
    expectFound(
      hostBuilder.build(),
      hostBuilder.root,
      pattern,
      [attachment],
    )
  })

  it('finds a spliced pattern deep inside nested cuts', () => {
    const pattern = unaryRefPattern()
    const hostBuilder = new DiagramBuilder()
    const outer = hostBuilder.cut(hostBuilder.root)
    const inner = hostBuilder.cut(outer)
    const attachment = bareWire(hostBuilder, hostBuilder.root)
    expectFound(hostBuilder.build(), inner, pattern, [attachment])
  })

  it('finds a spliced cut-subtree pattern with a crossing boundary', () => {
    const patternBuilder = new DiagramBuilder()
    const cut = patternBuilder.cut(patternBuilder.root)
    const ref = patternBuilder.ref(cut, 'P', relSig([IOTA]))
    const stub = patternBuilder.wire([
      { node: ref, port: { kind: 'arg', index: 0 } },
    ])
    const pattern = patternBuilder.buildOpen([stub])
    const hostBuilder = new DiagramBuilder()
    const attachment = bareWire(hostBuilder, hostBuilder.root)

    expectFound(
      hostBuilder.build(),
      hostBuilder.root,
      pattern,
      [attachment],
    )
  })

  it('finds a closed relational-atom pattern after splicing', () => {
    const patternBuilder = new DiagramBuilder()
    patternBuilder.atom(patternBuilder.root, relSig([IOTA]))
    const pattern = patternBuilder.buildOpen([])
    const hostBuilder = new DiagramBuilder()
    hostBuilder.ref(hostBuilder.root, 'Existing', relSig([]))

    expectFound(hostBuilder.build(), hostBuilder.root, pattern, [])
  })

  it('finds two distinct stubs spliced onto one repeated attachment', () => {
    const patternBuilder = new DiagramBuilder()
    const ref = patternBuilder.ref(
      patternBuilder.root,
      'P',
      relSig([IOTA, IOTA]),
    )
    const first = patternBuilder.wire([
      { node: ref, port: { kind: 'arg', index: 0 } },
    ])
    const second = patternBuilder.wire([
      { node: ref, port: { kind: 'arg', index: 1 } },
    ])
    const pattern = patternBuilder.buildOpen([first, second])
    const hostBuilder = new DiagramBuilder()
    const attachment = bareWire(hostBuilder, hostBuilder.root)

    expectFound(
      hostBuilder.build(),
      hostBuilder.root,
      pattern,
      [attachment, attachment],
    )
  })

  it('keeps attachment order index-aligned with distinct boundary wires', () => {
    const patternBuilder = new DiagramBuilder()
    const ref = patternBuilder.ref(
      patternBuilder.root,
      'P',
      relSig([IOTA, IOTA]),
    )
    const first = patternBuilder.wire([
      { node: ref, port: { kind: 'arg', index: 0 } },
    ])
    const second = patternBuilder.wire([
      { node: ref, port: { kind: 'arg', index: 1 } },
    ])
    const pattern = patternBuilder.buildOpen([first, second])
    const hostBuilder = new DiagramBuilder()
    const firstAttachment = bareWire(hostBuilder, hostBuilder.root)
    const secondAttachment = bareWire(hostBuilder, hostBuilder.root)
    const host = hostBuilder.build()

    expectFound(host, host.root, pattern, [firstAttachment, secondAttachment])
    expectFound(host, host.root, pattern, [secondAttachment, firstAttachment])
  })

  it('finds both an existing occurrence and a copy spliced into a cut', () => {
    const pattern = unaryRefPattern()
    const hostBuilder = new DiagramBuilder()
    const existing = hostBuilder.ref(
      hostBuilder.root,
      'P',
      relSig([IOTA]),
    )
    const hub = hostBuilder.ref(
      hostBuilder.root,
      'Hub',
      relSig([IOTA]),
    )
    const attachment = hostBuilder.wire([
      { node: existing, port: { kind: 'arg', index: 0 } },
      { node: hub, port: { kind: 'arg', index: 0 } },
    ])
    const cut = hostBuilder.cut(hostBuilder.root)
    const host = hostBuilder.build()
    const spliced = spliceSubgraph(host, cut, pattern, [attachment])
    const result = findOccurrences(spliced, pattern)

    expect(result.matches.map((match) => match.region).sort())
      .toEqual([host.root, cut].sort())
    for (const match of result.matches) {
      expect(match.attachments).toEqual([attachment])
    }
  })
})
