import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagram } from '../../../src/kernel/diagram/diagram'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
import { findOccurrences } from '../../../src/kernel/diagram/subgraph/match'
import { bareWire } from '../../fixtures/pins'

const rel2 = relSig([IOTA, IOTA])

/** Host: chain ref d0 -(w0)- ref d1 -(w1)- ref d2, ends pinned. Distinct
 *  defIds, so every ref has a unique content key. Copied from
 *  match-propagation.test.ts's chainHost. */
function chainHost() {
  return mkDiagram({
    root: 'root',
    regions: { root: { kind: 'sheet' } },
    nodes: {
      r0: { kind: 'ref', region: 'root', defId: 'd0', sig: rel2 },
      r1: { kind: 'ref', region: 'root', defId: 'd1', sig: rel2 },
      r2: { kind: 'ref', region: 'root', defId: 'd2', sig: rel2 },
      pL: { kind: 'identity', region: 'root', sig: IOTA, arity: 1 },
      pR: { kind: 'identity', region: 'root', sig: IOTA, arity: 1 },
    },
    wires: {
      end0: { sig: IOTA, endpoints: [
        { node: 'r0', port: { kind: 'arg', index: 0 } },
        { node: 'pL', port: { kind: 'identity', index: 0 } },
      ] },
      w0: { sig: IOTA, endpoints: [
        { node: 'r0', port: { kind: 'arg', index: 1 } },
        { node: 'r1', port: { kind: 'arg', index: 0 } },
      ] },
      w1: { sig: IOTA, endpoints: [
        { node: 'r1', port: { kind: 'arg', index: 1 } },
        { node: 'r2', port: { kind: 'arg', index: 0 } },
      ] },
      end1: { sig: IOTA, endpoints: [
        { node: 'r2', port: { kind: 'arg', index: 1 } },
        { node: 'pR', port: { kind: 'identity', index: 0 } },
      ] },
    },
  })
}

/** Pattern: the same chain graph, ids prefixed `p`, with its two end wires
 *  (still carrying their own pin nodes, exactly as in the host) exposed as
 *  the boundary. */
function chainPattern() {
  return mkDiagramWithBoundary(
    {
      root: 'proot',
      regions: { proot: { kind: 'sheet' } },
      nodes: {
        pr0: { kind: 'ref', region: 'proot', defId: 'd0', sig: rel2 },
        pr1: { kind: 'ref', region: 'proot', defId: 'd1', sig: rel2 },
        pr2: { kind: 'ref', region: 'proot', defId: 'd2', sig: rel2 },
        ppL: { kind: 'identity', region: 'proot', sig: IOTA, arity: 1 },
        ppR: { kind: 'identity', region: 'proot', sig: IOTA, arity: 1 },
      },
      wires: {
        pend0: { sig: IOTA, endpoints: [
          { node: 'pr0', port: { kind: 'arg', index: 0 } },
          { node: 'ppL', port: { kind: 'identity', index: 0 } },
        ] },
        pw0: { sig: IOTA, endpoints: [
          { node: 'pr0', port: { kind: 'arg', index: 1 } },
          { node: 'pr1', port: { kind: 'arg', index: 0 } },
        ] },
        pw1: { sig: IOTA, endpoints: [
          { node: 'pr1', port: { kind: 'arg', index: 1 } },
          { node: 'pr2', port: { kind: 'arg', index: 0 } },
        ] },
        pend1: { sig: IOTA, endpoints: [
          { node: 'pr2', port: { kind: 'arg', index: 1 } },
          { node: 'ppR', port: { kind: 'identity', index: 0 } },
        ] },
      },
    },
    ['pend0', 'pend1'],
  )
}

/** Host: one arity-2 identity `j` with each of its two ports pinned by its
 *  own unary identity (`pinU` via wire `u`, `pinV` via wire `v`). Pattern:
 *  an arity-2 identity with both ports exposed as bare boundary wires. */
function symmetricHost() {
  return mkDiagram({
    root: 'root',
    regions: { root: { kind: 'sheet' } },
    nodes: {
      j: { kind: 'identity', region: 'root', sig: IOTA, arity: 2 },
      pinU: { kind: 'identity', region: 'root', sig: IOTA, arity: 1 },
      pinV: { kind: 'identity', region: 'root', sig: IOTA, arity: 1 },
    },
    wires: {
      u: { sig: IOTA, endpoints: [
        { node: 'j', port: { kind: 'identity', index: 0 } },
        { node: 'pinU', port: { kind: 'identity', index: 0 } },
      ] },
      v: { sig: IOTA, endpoints: [
        { node: 'j', port: { kind: 'identity', index: 1 } },
        { node: 'pinV', port: { kind: 'identity', index: 0 } },
      ] },
    },
  })
}

function symmetricPattern() {
  return mkDiagramWithBoundary(
    {
      root: 'proot',
      regions: { proot: { kind: 'sheet' } },
      nodes: { pj: { kind: 'identity', region: 'proot', sig: IOTA, arity: 2 } },
      wires: {
        x: { sig: IOTA, endpoints: [{ node: 'pj', port: { kind: 'identity', index: 0 } }] },
        y: { sig: IOTA, endpoints: [{ node: 'pj', port: { kind: 'identity', index: 1 } }] },
      },
    },
    ['x', 'y'],
  )
}

describe('exact occurrence matching adversarial battery', () => {
  it('matches exact reference content with positional wiring intact', () => {
    const patternBuilder = new DiagramBuilder()
    const patternRef = patternBuilder.ref(
      patternBuilder.root,
      'P',
      relSig([IOTA, IOTA]),
    )
    const firstStub = patternBuilder.wire([
      { node: patternRef, port: { kind: 'arg', index: 0 } },
    ])
    const secondStub = patternBuilder.wire([
      { node: patternRef, port: { kind: 'arg', index: 1 } },
    ])
    const pattern = patternBuilder.buildOpen([firstStub, secondStub])

    const hostBuilder = new DiagramBuilder()
    const hostRef = hostBuilder.ref(
      hostBuilder.root,
      'P',
      relSig([IOTA, IOTA]),
    )
    const firstWire = hostBuilder.wire([
      { node: hostRef, port: { kind: 'arg', index: 0 } },
    ])
    const secondWire = hostBuilder.wire([
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
    const pattern = patternBuilder.buildOpen([])
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
    const pattern = patternBuilder.buildOpen([])
    const hostBuilder = new DiagramBuilder()
    hostBuilder.ref(hostBuilder.root, 'P', relSig([]))
    hostBuilder.ref(hostBuilder.root, 'P', relSig([]))

    expect(findOccurrences(hostBuilder.build(), pattern).matches).toHaveLength(1)
  })

  it('retains distinct partial-selection footprints', () => {
    const patternBuilder = new DiagramBuilder()
    patternBuilder.ref(patternBuilder.root, 'P', relSig([]))
    const pattern = patternBuilder.buildOpen([])
    const hostBuilder = new DiagramBuilder()
    hostBuilder.ref(hostBuilder.root, 'P', relSig([]))
    hostBuilder.ref(hostBuilder.root, 'P', relSig([]))

    expect(findOccurrences(hostBuilder.build(), pattern).matches).toHaveLength(2)
  })

  it('uses exact wire sets below the root and subset semantics at the root', () => {
    const nestedPatternBuilder = new DiagramBuilder()
    const patternCut = nestedPatternBuilder.cut(nestedPatternBuilder.root)
    bareWire(nestedPatternBuilder, patternCut)
    const nestedPattern = nestedPatternBuilder.buildOpen([])

    const nestedHostBuilder = new DiagramBuilder()
    const hostCut = nestedHostBuilder.cut(nestedHostBuilder.root)
    bareWire(nestedHostBuilder, hostCut)
    bareWire(nestedHostBuilder, hostCut)
    expect(findOccurrences(nestedHostBuilder.build(), nestedPattern).matches)
      .toHaveLength(0)

    const rootPatternBuilder = new DiagramBuilder()
    bareWire(rootPatternBuilder, rootPatternBuilder.root)
    const rootPattern = rootPatternBuilder.buildOpen([])
    const rootHostBuilder = new DiagramBuilder()
    bareWire(rootHostBuilder, rootHostBuilder.root)
    bareWire(rootHostBuilder, rootHostBuilder.root)
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
    patternBuilder.wire([
      { node: patternRef, port: { kind: 'arg', index: 0 } },
    ])
    const pattern = patternBuilder.buildOpen([])

    const hostBuilder = new DiagramBuilder()
    const hostCut = hostBuilder.cut(hostBuilder.root)
    const hostRef = hostBuilder.ref(hostCut, 'P', relSig([IOTA]))
    // The host's wire is quantified at the root, the pattern's inside its cut.
    const hostArgument = hostBuilder.wire([
      { node: hostRef, port: { kind: 'arg', index: 0 } },
    ])
    hostBuilder.pin(hostArgument, hostBuilder.root)

    expect(findOccurrences(hostBuilder.build(), pattern).matches).toHaveLength(0)
  })

  it('rejects a scope swap that preserves per-region wire counts', () => {
    const patternBuilder = new DiagramBuilder()
    const patternCut = patternBuilder.cut(patternBuilder.root)
    const patternA = patternBuilder.ref(patternCut, 'A', relSig([IOTA]))
    const patternB = patternBuilder.ref(patternCut, 'B', relSig([IOTA]))
    patternBuilder.wire([
      { node: patternA, port: { kind: 'arg', index: 0 } },
    ])
    const patternOuter = patternBuilder.wire([
      { node: patternB, port: { kind: 'arg', index: 0 } },
    ])
    patternBuilder.pin(patternOuter, patternBuilder.root)
    const pattern = patternBuilder.buildOpen([])

    const hostBuilder = new DiagramBuilder()
    const hostCut = hostBuilder.cut(hostBuilder.root)
    const hostA = hostBuilder.ref(hostCut, 'A', relSig([IOTA]))
    const hostB = hostBuilder.ref(hostCut, 'B', relSig([IOTA]))
    const hostOuter = hostBuilder.wire([
      { node: hostA, port: { kind: 'arg', index: 0 } },
    ])
    hostBuilder.pin(hostOuter, hostBuilder.root)
    hostBuilder.wire([
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
    const stub = patternBuilder.wire([
      { node: first, port: { kind: 'arg', index: 0 } },
      { node: second, port: { kind: 'arg', index: 0 } },
    ])
    const pattern = patternBuilder.buildOpen([stub])

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
    sharedBuilder.wire([
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
      return builder.buildOpen([])
    }
    const hostBuilder = new DiagramBuilder()
    hostBuilder.atom(hostBuilder.root, relSig([IOTA]))
    const host = hostBuilder.build()

    expect(findOccurrences(host, pattern(1)).matches).toHaveLength(1)
    expect(findOccurrences(host, pattern(2)).matches).toHaveLength(0)
  })
})

describe('propagation-driven matching does no blind search', () => {
  it('a rigid chain is matched in exactly one placement per element', () => {
    const host = chainHost()
    const pattern = chainPattern()
    const result = findOccurrences(host, pattern, {})
    expect(result.status).toBe('complete')
    expect(result.matches).toHaveLength(1)
    // Derivation (from match.ts's spend(), called once per tryAssign, which
    // fires once per pattern region/node/wire placement attempt):
    //   - The pattern's elements: 1 region (proot) + 5 nodes (pr0, pr1, pr2,
    //     ppL, ppR) + 4 wires (pend0, pw0, pw1, pend1) = 10.
    //   - The host has exactly one region ('root'), so the root-candidate
    //     loop (`for (const hostRoot of [...cands0.region.get(root)!])`)
    //     probes it exactly once — that probe IS the region's placement
    //     attempt, already counted above.
    //   - Every ref has a globally distinct defId (d0/d1/d2), so content-key
    //     filtering alone pins each pr_/pw_/pend_ candidate set to size 1
    //     before propagation even runs the positional-port and wire-endpoint
    //     arcs; identity-port arcs (family 4) then pin ppL/ppR to {pL}/{pR}
    //     via their unique end wires. Every candidate set is a singleton by
    //     the time it is picked, so `pickNext` never offers more than one
    //     candidate per element: zero dead branches, one tryAssign call per
    //     element, total spend = 10.
    expect(result.explorationSteps).toBe(10)
  })

  it('symmetric boundary wires yield exactly the distinct attachment vectors', () => {
    const host = symmetricHost()
    const pattern = symmetricPattern()
    const result = findOccurrences(host, pattern, {})
    // Identity ports carry no positional identity (diagram.ts's
    // endpointPositionKey / refine.ts's endpointKey both collapse every
    // identity port to the single key 'i'), so wires x and y each keep {u, v}
    // as their candidate set straight through propagation — the search must
    // try both bindings for each, and identityMatches (the unordered
    // incident-wire check) accepts exactly the two that pair x and y with
    // distinct host wires.
    expect(result.matches.map((m) => [...m.attachments]).sort()).toEqual([['u', 'v'], ['v', 'u']])
  })
})
