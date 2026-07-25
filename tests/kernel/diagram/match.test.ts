import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagram } from '../../../src/kernel/diagram/diagram'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
import { findOccurrences } from '../../../src/kernel/diagram/subgraph/match'
import { checkOccurrenceCertificate } from '../../../src/kernel/diagram/subgraph/occurrence-certificate'

function unaryPattern(defId = 'P') {
  const builder = new DiagramBuilder()
  const node = builder.ref(builder.root, defId, relSig([IOTA]))
  const boundary = builder.wire(builder.root, [
    { node, port: { kind: 'arg', index: 0 } },
  ])
  return mkDiagramWithBoundary(builder.build(), [boundary])
}

function unaryHost(defId = 'P') {
  const builder = new DiagramBuilder()
  const node = builder.ref(builder.root, defId, relSig([IOTA]))
  const wire = builder.wire(builder.root, [
    { node, port: { kind: 'arg', index: 0 } },
  ])
  return { diagram: builder.build(), node, wire }
}

describe('exact occurrence matching', () => {
  it('finds and certifies an exact ref occurrence', () => {
    const host = unaryHost()
    const pattern = unaryPattern()
    const result = findOccurrences(host.diagram, pattern)

    expect(result.status).toBe('complete')
    expect(result.matches).toHaveLength(1)
    expect(result.explorationSteps).toBeGreaterThan(0)
    expect(result.matches[0]?.attachments).toEqual([host.wire])
    expect(checkOccurrenceCertificate(host.diagram, pattern, result.matches[0]!))
      .toEqual({ ok: true })
  })

  it('uses exact node content and proper-subtree structure', () => {
    expect(findOccurrences(unaryHost('Q').diagram, unaryPattern('P')).matches)
      .toHaveLength(0)

    const patternBuilder = new DiagramBuilder()
    const patternCut = patternBuilder.cut(patternBuilder.root)
    patternBuilder.ref(patternCut, 'P', relSig([]))
    const pattern = mkDiagramWithBoundary(patternBuilder.build(), [])

    const hostBuilder = new DiagramBuilder()
    const hostCut = hostBuilder.cut(hostBuilder.root)
    hostBuilder.ref(hostCut, 'P', relSig([]))
    hostBuilder.ref(hostCut, 'extra', relSig([]))
    expect(findOccurrences(hostBuilder.build(), pattern).matches).toHaveLength(0)
  })

  it('allows extra host endpoints only at the open boundary', () => {
    const builder = new DiagramBuilder()
    const target = builder.ref(builder.root, 'P', relSig([IOTA]))
    const extra = builder.ref(builder.root, 'Q', relSig([IOTA]))
    builder.wire(builder.root, [
      { node: target, port: { kind: 'arg', index: 0 } },
      { node: extra, port: { kind: 'arg', index: 0 } },
    ])

    expect(findOccurrences(builder.build(), unaryPattern()).matches).toHaveLength(1)
  })

  it('reports graph-exploration exhaustion without semantic verdict fields', () => {
    const host = unaryHost()
    const exhausted = findOccurrences(host.diagram, unaryPattern(), {
      explorationFuel: 1,
    })
    const complete = findOccurrences(host.diagram, unaryPattern())

    expect(exhausted.status).toBe('exhausted')
    expect(exhausted.matches).toEqual([])
    expect(Object.keys(complete).sort()).toEqual([
      'explorationSteps',
      'matches',
      'status',
    ])
    expect(() => findOccurrences(host.diagram, unaryPattern(), {
      explorationFuel: 0,
    })).toThrowError(/positive safe integer/)
  })

  it('requires a seed for bare boundary wires and validates the seed', () => {
    const pattern = mkDiagramWithBoundary(mkDiagram({
      root: 'p0',
      regions: { p0: { kind: 'sheet' } },
      wires: {
        stub: { scope: 'p0', sig: IOTA, endpoints: [] },
      },
    }), ['stub'])
    const host = mkDiagram({
      root: 'r0',
      regions: { r0: { kind: 'sheet' } },
      wires: {
        target: { scope: 'r0', sig: IOTA, endpoints: [] },
      },
    })

    expect(() => findOccurrences(host, pattern)).toThrowError(/supply its attachment/)
    expect(findOccurrences(host, pattern, { attachments: ['target'] }).matches)
      .toHaveLength(1)
    expect(() => findOccurrences(host, pattern, { attachments: [] }))
      .toThrowError(/index-aligned/)
  })

  it('matches identity incidences as an unordered mapped multiset', () => {
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
          scope: 'p0',
          sig: IOTA,
          endpoints: [{ node: 'eq', port: { kind: 'identity', index: 0 } }],
        },
        right: {
          scope: 'p0',
          sig: IOTA,
          endpoints: [{ node: 'eq', port: { kind: 'identity', index: 1 } }],
        },
      },
    }), ['left', 'right'])
    const host = mkDiagram({
      root: 'r0',
      regions: {
        r0: { kind: 'sheet' },
        r1: { kind: 'cut', parent: 'r0' },
      },
      nodes: {
        identity: { kind: 'identity', region: 'r1', sig: IOTA, arity: 2 },
      },
      wires: {
        a: {
          scope: 'r0',
          sig: IOTA,
          endpoints: [{ node: 'identity', port: { kind: 'identity', index: 1 } }],
        },
        b: {
          scope: 'r0',
          sig: IOTA,
          endpoints: [{ node: 'identity', port: { kind: 'identity', index: 0 } }],
        },
      },
    })

    expect(findOccurrences(host, pattern, {
      inRegion: 'r0',
      attachments: ['a', 'b'],
    }).matches).toHaveLength(1)
  })
})
