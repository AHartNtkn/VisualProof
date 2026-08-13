import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagram } from '../../../src/kernel/diagram/diagram'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
import { findOccurrences } from '../../../src/kernel/diagram/subgraph/match'
import {
  checkOccurrenceCertificate,
  type OccurrenceCertificate,
} from '../../../src/kernel/diagram/subgraph/occurrence-certificate'
import { occurrenceToSelection } from '../../../src/kernel/diagram/subgraph/occurrence'

function fixture() {
  const patternBuilder = new DiagramBuilder()
  const patternNode = patternBuilder.ref(patternBuilder.root, 'P', relSig([IOTA]))
  const patternWire = patternBuilder.wire( [
    { node: patternNode, port: { kind: 'arg', index: 0 } },
  ])
  const pattern = mkDiagramWithBoundary(patternBuilder.build(), [patternWire])

  const hostBuilder = new DiagramBuilder()
  const hostNode = hostBuilder.ref(hostBuilder.root, 'P', relSig([IOTA]))
  const extra = hostBuilder.ref(hostBuilder.root, 'Q', relSig([IOTA]))
  const hostWire = hostBuilder.wire( [
    { node: hostNode, port: { kind: 'arg', index: 0 } },
    { node: extra, port: { kind: 'arg', index: 0 } },
  ])
  const host = hostBuilder.build()
  const occurrence = findOccurrences(host, pattern).matches[0]!
  return {
    host,
    pattern,
    occurrence,
    patternNode,
    hostNode,
    extra,
    hostWire,
  }
}

function roundTripCertificate(
  certificate: OccurrenceCertificate,
): OccurrenceCertificate {
  const encoded = JSON.parse(JSON.stringify({
    region: certificate.region,
    regionMap: [...certificate.regionMap],
    nodeMap: [...certificate.nodeMap],
    wireMap: [...certificate.wireMap],
    attachments: [...certificate.attachments],
  })) as {
    region: string
    regionMap: [string, string][]
    nodeMap: [string, string][]
    wireMap: [string, string][]
    attachments: string[]
  }
  return {
    region: encoded.region,
    regionMap: new Map(encoded.regionMap),
    nodeMap: new Map(encoded.nodeMap),
    wireMap: new Map(encoded.wireMap),
    attachments: encoded.attachments,
  }
}

describe('occurrence certificates', () => {
  it('accepts the exact matcher-produced witness', () => {
    const value = fixture()
    expect(checkOccurrenceCertificate(value.host, value.pattern, value.occurrence))
      .toEqual({ ok: true })
  })

  it('round-trips a certificate as plain data and replays it exactly', () => {
    const value = fixture()
    const replayed = roundTripCertificate(value.occurrence)

    expect(replayed).toEqual(value.occurrence)
    expect(checkOccurrenceCertificate(value.host, value.pattern, replayed))
      .toEqual({ ok: true })
  })

  it('rejects unknown occurrence regions and incomplete map domains', () => {
    const value = fixture()
    const unknownRegion = {
      ...value.occurrence,
      region: 'ghost',
    }
    expect(checkOccurrenceCertificate(value.host, value.pattern, unknownRegion))
      .toMatchObject({ ok: false, reason: expect.stringMatching(/does not exist/) })

    const missingNode = {
      ...value.occurrence,
      nodeMap: new Map(),
    }
    expect(checkOccurrenceCertificate(value.host, value.pattern, missingNode))
      .toMatchObject({ ok: false, reason: expect.stringMatching(/node map/) })
  })

  it('rejects incompatible node and missing wire images', () => {
    const value = fixture()
    const wrongNode = {
      ...value.occurrence,
      nodeMap: new Map([[value.patternNode, value.extra]]),
    }
    expect(checkOccurrenceCertificate(value.host, value.pattern, wrongNode))
      .toMatchObject({
        ok: false,
        reason: expect.stringMatching(/reference.*incompatible image/),
      })

    const missingWire = {
      ...value.occurrence,
      wireMap: new Map(
        [...value.occurrence.wireMap].map(([patternWire]) =>
          [patternWire, 'ghost'] as const,
        ),
      ),
    }
    expect(checkOccurrenceCertificate(value.host, value.pattern, missingWire))
      .toMatchObject({
        ok: false,
        reason: expect.stringMatching(/mapped wire 'ghost'.*does not exist/),
      })
  })

  it('rejects incorrect attachment vector length and content', () => {
    const value = fixture()
    const missingAttachment = {
      ...value.occurrence,
      attachments: [],
    }
    expect(checkOccurrenceCertificate(
      value.host,
      value.pattern,
      missingAttachment,
    )).toMatchObject({
      ok: false,
      reason: expect.stringMatching(/attachment vector length/),
    })

    const wrongAttachment = {
      ...value.occurrence,
      attachments: ['ghost'],
    }
    expect(checkOccurrenceCertificate(value.host, value.pattern, wrongAttachment))
      .toMatchObject({ ok: false, reason: expect.stringMatching(/attachment 0/) })
  })

  it('rejects a replay whose mapped proper subtree has extra content', () => {
    const patternBuilder = new DiagramBuilder()
    const patternCut = patternBuilder.cut(patternBuilder.root)
    const patternNode = patternBuilder.ref(patternCut, 'P', relSig([]))
    const pattern = mkDiagramWithBoundary(patternBuilder.build(), [])

    const hostBuilder = new DiagramBuilder()
    const hostCut = hostBuilder.cut(hostBuilder.root)
    const hostNode = hostBuilder.ref(hostCut, 'P', relSig([]))
    hostBuilder.ref(hostCut, 'Extra', relSig([]))
    const host = hostBuilder.build()
    const certificate: OccurrenceCertificate = {
      region: host.root,
      regionMap: new Map([
        [pattern.diagram.root, host.root],
        [patternCut, hostCut],
      ]),
      nodeMap: new Map([[patternNode, hostNode]]),
      wireMap: new Map(),
      attachments: [],
    }

    expect(checkOccurrenceCertificate(host, pattern, certificate))
      .toMatchObject({
        ok: false,
        reason: expect.stringMatching(/extra or missing nodes/),
      })
  })

  it('preserves exact unordered identity incidence multisets', () => {
    const pattern = mkDiagramWithBoundary(mkDiagram({
      root: 'p0',
      regions: {
        p0: { kind: 'sheet' },
        p1: { kind: 'cut', parent: 'p0' },
      },
      nodes: {
        eq: { kind: 'identity', region: 'p1', sig: IOTA, arity: 2 },
      },
      wires: {
        left: {
          sig: IOTA,
          endpoints: [{
            node: 'eq',
            port: { kind: 'identity', index: 0 },
          }],
        },
        right: {
          sig: IOTA,
          endpoints: [{
            node: 'eq',
            port: { kind: 'identity', index: 1 },
          }],
        },
      },
    }), ['left', 'right'])
    const host = mkDiagram({
      root: 'h0',
      regions: {
        h0: { kind: 'sheet' },
        h1: { kind: 'cut', parent: 'h0' },
      },
      nodes: {
        identity: { kind: 'identity', region: 'h1', sig: IOTA, arity: 2 },
      },
      wires: {
        a: {
          sig: IOTA,
          endpoints: [{
            node: 'identity',
            port: { kind: 'identity', index: 1 },
          }],
        },
        b: {
          sig: IOTA,
          endpoints: [{
            node: 'identity',
            port: { kind: 'identity', index: 0 },
          }],
        },
      },
    })
    const occurrence = findOccurrences(host, pattern, {
      inRegion: host.root,
      attachments: ['a', 'b'],
    }).matches[0]!

    expect(checkOccurrenceCertificate(host, pattern, occurrence))
      .toEqual({ ok: true })

    const aliased: OccurrenceCertificate = {
      ...occurrence,
      wireMap: new Map([
        ['left', 'a'],
        ['right', 'a'],
      ]),
      attachments: ['a', 'a'],
    }
    expect(checkOccurrenceCertificate(host, pattern, aliased))
      .toMatchObject({
        ok: false,
        reason: expect.stringMatching(
          /identity 'eq'.*unordered wire incidences/,
        ),
      })
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
