import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
import { findOccurrences } from '../../../src/kernel/diagram/subgraph/match'
import { checkOccurrenceCertificate } from '../../../src/kernel/diagram/subgraph/occurrence-certificate'
import { occurrenceToSelection } from '../../../src/kernel/diagram/subgraph/occurrence'

function fixture() {
  const patternBuilder = new DiagramBuilder()
  const patternNode = patternBuilder.ref(patternBuilder.root, 'P', relSig([IOTA]))
  const patternWire = patternBuilder.wire(patternBuilder.root, [
    { node: patternNode, port: { kind: 'arg', index: 0 } },
  ])
  const pattern = mkDiagramWithBoundary(patternBuilder.build(), [patternWire])

  const hostBuilder = new DiagramBuilder()
  const hostNode = hostBuilder.ref(hostBuilder.root, 'P', relSig([IOTA]))
  const extra = hostBuilder.ref(hostBuilder.root, 'Q', relSig([IOTA]))
  const hostWire = hostBuilder.wire(hostBuilder.root, [
    { node: hostNode, port: { kind: 'arg', index: 0 } },
    { node: extra, port: { kind: 'arg', index: 0 } },
  ])
  const host = hostBuilder.build()
  const occurrence = findOccurrences(host, pattern).matches[0]!
  return { host, pattern, occurrence, patternNode, hostNode, hostWire }
}

describe('occurrence certificates', () => {
  it('accepts the exact matcher-produced witness', () => {
    const value = fixture()
    expect(checkOccurrenceCertificate(value.host, value.pattern, value.occurrence))
      .toEqual({ ok: true })
  })

  it('rejects incomplete maps and incorrect attachment vectors', () => {
    const value = fixture()
    const missingNode = {
      ...value.occurrence,
      nodeMap: new Map(),
    }
    expect(checkOccurrenceCertificate(value.host, value.pattern, missingNode))
      .toMatchObject({ ok: false, reason: expect.stringMatching(/node map/) })

    const wrongAttachment = {
      ...value.occurrence,
      attachments: ['ghost'],
    }
    expect(checkOccurrenceCertificate(value.host, value.pattern, wrongAttachment))
      .toMatchObject({ ok: false, reason: expect.stringMatching(/attachment 0/) })
  })

  it('converts only occurrence content, excluding boundary attachment wires', () => {
    const value = fixture()
    const selection = occurrenceToSelection(
      value.host,
      value.pattern,
      value.occurrence,
    )

    expect(selection.region).toBe(value.host.root)
    expect(selection.nodes).toEqual([value.hostNode])
    expect(selection.wires).toEqual([])
    expect(selection.regions).toEqual([])
  })
})
