import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagram } from '../../../src/kernel/diagram/diagram'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
import { findOccurrences } from '../../../src/kernel/diagram/subgraph/match'
import { checkOccurrenceCertificate } from '../../../src/kernel/diagram/subgraph/occurrence-certificate'
import { bareWireParts } from '../../fixtures/pins'
import { parseTerm } from '../../../src/kernel/term/parse'

function unaryPattern(defId = 'P') {
  const builder = new DiagramBuilder()
  const node = builder.ref(builder.root, defId, relSig([IOTA]))
  const boundary = builder.wire( [
    { node, port: { kind: 'arg', index: 0 } },
  ])
  return builder.buildOpen([boundary])
}

function unaryHost(defId = 'P') {
  const builder = new DiagramBuilder()
  const node = builder.ref(builder.root, defId, relSig([IOTA]))
  const wire = builder.wire( [
    { node, port: { kind: 'arg', index: 0 } },
  ])
  return { diagram: builder.build(), node, wire }
}

describe('exact occurrence matching', () => {
  it('matches exact nameless term content and ordered free-slot ports', () => {
    const make = (source: string) => {
      const builder = new DiagramBuilder()
      const node = builder.term(builder.root, parseTerm(source).term, 1)
      const output = builder.wire([{ node, port: { kind: 'output' } }])
      const free = builder.wire([{ node, port: { kind: 'free', index: 0 } }])
      return { diagram: builder.build(), node, output, free }
    }
    const host = make('\\x. x y')
    const matching = make('\\z. z y')
    const different = make('\\x. y x')
    const matchingPattern = mkDiagramWithBoundary(matching.diagram, [matching.output, matching.free])
    const differentPattern = mkDiagramWithBoundary(different.diagram, [different.output, different.free])

    expect(findOccurrences(host.diagram, matchingPattern, {
      inRegion: host.diagram.root,
      attachments: [host.output, host.free],
    }).matches).toHaveLength(1)
    expect(findOccurrences(host.diagram, differentPattern, {
      inRegion: host.diagram.root,
      attachments: [host.output, host.free],
    }).matches).toHaveLength(0)
  })

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
    const pattern = patternBuilder.buildOpen([])

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
    builder.wire( [
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

  it('requires a seed for endpoint-free boundary wires and validates the seed', () => {
    // A wire exposed at two boundary positions has both its ends there and no
    // endpoint at all, so the search has nothing to anchor on and the caller
    // must name the host line.
    const twiceExposed = mkDiagramWithBoundary({
      root: 'p0',
      regions: { p0: { kind: 'sheet' } },
      nodes: {},
      wires: { stub: { sig: IOTA, endpoints: [] } },
    }, ['stub', 'stub'])
    const target = bareWireParts('target', 'r0')
    const host = mkDiagram({
      root: 'r0',
      regions: { r0: { kind: 'sheet' } },
      nodes: target.nodes,
      wires: target.wires,
    })

    expect(() => findOccurrences(host, twiceExposed)).toThrowError(/supply its attachment/)
    expect(findOccurrences(host, twiceExposed, { attachments: ['target', 'target'] }).matches)
      .toHaveLength(1)
    expect(() => findOccurrences(host, twiceExposed, { attachments: [] }))
      .toThrowError(/index-aligned/)

    // Exposed once, the same line ends in a point, and that point anchors the
    // search on its own — no seed needed.
    const patternStub = bareWireParts('stub', 'p0')
    const onceExposed = mkDiagramWithBoundary({
      root: 'p0',
      regions: { p0: { kind: 'sheet' } },
      nodes: patternStub.nodes,
      wires: patternStub.wires,
    }, ['stub'])
    expect(findOccurrences(host, onceExposed).matches).toHaveLength(1)
  })

  it('matches identity incidences as an unordered mapped multiset', () => {
    const pattern = mkDiagramWithBoundary({
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
          endpoints: [{ node: 'eq', port: { kind: 'identity', index: 0 } }],
        },
        right: {
          sig: IOTA,
          endpoints: [{ node: 'eq', port: { kind: 'identity', index: 1 } }],
        },
      },
    }, ['left', 'right'])
    const host = mkDiagram({
      root: 'r0',
      regions: {
        r0: { kind: 'sheet' },
        r1: { kind: 'cut', parent: 'r0' },
      },
      nodes: {
        identity: { kind: 'identity', region: 'r1', sig: IOTA, arity: 2 },
        aPin: { kind: 'identity', region: 'r0', sig: IOTA, arity: 1 },
        bPin: { kind: 'identity', region: 'r0', sig: IOTA, arity: 1 },
      },
      wires: {
        a: {
          sig: IOTA,
          endpoints: [
            { node: 'identity', port: { kind: 'identity', index: 1 } },
            { node: 'aPin', port: { kind: 'identity', index: 0 } },
          ],
        },
        b: {
          sig: IOTA,
          endpoints: [
            { node: 'identity', port: { kind: 'identity', index: 0 } },
            { node: 'bPin', port: { kind: 'identity', index: 0 } },
          ],
        },
      },
    })

    expect(findOccurrences(host, pattern, {
      inRegion: 'r0',
      attachments: ['a', 'b'],
    }).matches).toHaveLength(1)
  })
})
