import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import type {
  Diagram,
  Endpoint,
  NodeId,
  RegionId,
} from '../../../src/kernel/diagram/diagram'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
import {
  __benchCounter,
  findOccurrences,
} from '../../../src/kernel/diagram/subgraph/match'

function choose(total: number, selected: number): number {
  let result = 1
  for (let index = 0; index < selected; index++) {
    result = (result * (total - index)) / (index + 1)
  }
  return Math.round(result)
}

function identicalRefs(count: number): Diagram {
  const builder = new DiagramBuilder()
  for (let index = 0; index < count; index++) {
    builder.ref(builder.root, 'P', relSig([]))
  }
  return builder.build()
}

function identicalPattern(count: number) {
  return mkDiagramWithBoundary(identicalRefs(count), [])
}

describe('exploration matcher exhaustive assignment and footprint quotient', () => {
  function shared(count: number): Diagram {
    const builder = new DiagramBuilder()
    const endpoints: Endpoint[] = []
    for (let index = 0; index < count; index++) {
      const ref = builder.ref(builder.root, 'P', relSig([IOTA]))
      endpoints.push({ node: ref, port: { kind: 'arg', index: 0 } })
    }
    builder.wire( endpoints)
    return builder.build()
  }

  it('explores symmetric bijections but returns their one structural footprint', () => {
    __benchCounter.n = 0
    const result = findOccurrences(
      shared(4),
      mkDiagramWithBoundary(shared(4), []),
    )

    expect(result.status).toBe('complete')
    expect(result.matches).toHaveLength(1)
    expect(__benchCounter.n).toBeGreaterThan(4)
  })

  it('returns explicit exhaustion before backtracking completes', () => {
    const result = findOccurrences(
      identicalRefs(4),
      identicalPattern(2),
      { explorationFuel: 1, inRegion: 'r0' },
    )

    expect(result.status).toBe('exhausted')
    expect(result.matches.length).toBeLessThan(choose(4, 2))
    expect(result.explorationSteps).toBe(1)
  })

  it('returns every exact match when exploration fuel is sufficient', () => {
    const result = findOccurrences(
      identicalRefs(4),
      identicalPattern(2),
      { explorationFuel: 100_000, inRegion: 'r0' },
    )

    expect(result.status).toBe('complete')
    expect(result.matches).toHaveLength(choose(4, 2))
    expect(result.explorationSteps).toBeGreaterThan(1)
  })

  it('reports exhaustion when the budget stops inside a finite injection space', () => {
    const result = findOccurrences(
      identicalRefs(3),
      identicalPattern(3),
      { explorationFuel: 3, inRegion: 'r0' },
    )

    expect(result.status).toBe('exhausted')
    expect(result.explorationSteps).toBe(3)
  })
})

describe('exploration matcher symmetry completeness', () => {
  for (const [selected, total] of [
    [1, 3],
    [2, 4],
    [3, 5],
    [3, 3],
    [2, 5],
    [4, 6],
  ] as const) {
    it(`finds C(${total}, ${selected}) distinct identical-ref footprints`, () => {
      const result = findOccurrences(
        identicalRefs(total),
        identicalPattern(selected),
        { inRegion: 'r0' },
      )
      expect(result.matches).toHaveLength(choose(total, selected))
    })
  }

  it('collapses symmetric child-region bijections without losing distinct pairs', () => {
    const patternBuilder = new DiagramBuilder()
    for (let index = 0; index < 2; index++) {
      const cut = patternBuilder.cut(patternBuilder.root)
      patternBuilder.ref(cut, 'P', relSig([]))
    }
    const pattern = mkDiagramWithBoundary(patternBuilder.build(), [])

    const hostBuilder = new DiagramBuilder()
    for (let index = 0; index < 3; index++) {
      const cut = hostBuilder.cut(hostBuilder.root)
      hostBuilder.ref(cut, 'P', relSig([]))
    }
    const result = findOccurrences(
      hostBuilder.build(),
      pattern,
      { inRegion: hostBuilder.root },
    )

    expect(result.matches).toHaveLength(choose(3, 2))
  })

  it('does not collapse distinct open wirings to distinguishable hubs', () => {
    const patternBuilder = new DiagramBuilder()
    const patternRef = patternBuilder.ref(
      patternBuilder.root,
      'P',
      relSig([IOTA]),
    )
    const stub = patternBuilder.wire( [
      { node: patternRef, port: { kind: 'arg', index: 0 } },
    ])
    const pattern = mkDiagramWithBoundary(patternBuilder.build(), [stub])

    const hostBuilder = new DiagramBuilder()
    const first = hostBuilder.ref(hostBuilder.root, 'P', relSig([IOTA]))
    const second = hostBuilder.ref(hostBuilder.root, 'P', relSig([IOTA]))
    const firstHub = hostBuilder.ref(
      hostBuilder.root,
      'FirstHub',
      relSig([IOTA]),
    )
    const secondHub = hostBuilder.ref(
      hostBuilder.root,
      'SecondHub',
      relSig([IOTA]),
    )
    const firstWire = hostBuilder.wire( [
      { node: first, port: { kind: 'arg', index: 0 } },
      { node: firstHub, port: { kind: 'arg', index: 0 } },
    ])
    const secondWire = hostBuilder.wire( [
      { node: second, port: { kind: 'arg', index: 0 } },
      { node: secondHub, port: { kind: 'arg', index: 0 } },
    ])
    const result = findOccurrences(
      hostBuilder.build(),
      pattern,
      { inRegion: hostBuilder.root },
    )

    expect(result.matches).toHaveLength(2)
    expect(new Set(result.matches.map((match) => match.attachments[0])))
      .toEqual(new Set([firstWire, secondWire]))
  })

  it('makes seeded results equal the corresponding unseeded filter', () => {
    const patternBuilder = new DiagramBuilder()
    const patternRef = patternBuilder.ref(
      patternBuilder.root,
      'P',
      relSig([IOTA]),
    )
    const stub = patternBuilder.wire( [
      { node: patternRef, port: { kind: 'arg', index: 0 } },
    ])
    const pattern = mkDiagramWithBoundary(patternBuilder.build(), [stub])

    const hostBuilder = new DiagramBuilder()
    const first = hostBuilder.ref(hostBuilder.root, 'P', relSig([IOTA]))
    const second = hostBuilder.ref(hostBuilder.root, 'P', relSig([IOTA]))
    const firstWire = hostBuilder.wire( [
      { node: first, port: { kind: 'arg', index: 0 } },
    ])
    hostBuilder.wire( [
      { node: second, port: { kind: 'arg', index: 0 } },
    ])
    const host = hostBuilder.build()
    const unseeded = findOccurrences(host, pattern, { inRegion: host.root })
    const seeded = findOccurrences(host, pattern, {
      inRegion: host.root,
      attachments: [firstWire],
    })

    expect(seeded.matches).toEqual(
      unseeded.matches.filter((match) => match.attachments[0] === firstWire),
    )
    expect(seeded.matches).toHaveLength(1)
  })
})

function mulberry32(seed: number): () => number {
  let state = seed >>> 0
  return () => {
    state |= 0
    state = (state + 0x6d2b79f5) | 0
    let value = Math.imul(state ^ (state >>> 15), 1 | state)
    value = (value + Math.imul(value ^ (value >>> 7), 61 | value)) ^ value
    return ((value ^ (value >>> 14)) >>> 0) / 4_294_967_296
  }
}

function randomClosed(rng: () => number): Diagram {
  const builder = new DiagramBuilder()
  const regions: RegionId[] = [builder.root]
  const cutCount = Math.floor(rng() * 3)
  for (let index = 0; index < cutCount; index++) {
    regions.push(
      builder.cut(regions[Math.floor(rng() * regions.length)]!),
    )
  }
  const nodeCount = 1 + Math.floor(rng() * 4)
  const definitions = ['P', 'Q', 'R']
  for (let index = 0; index < nodeCount; index++) {
    builder.ref(
      regions[Math.floor(rng() * regions.length)]!,
      definitions[Math.floor(rng() * definitions.length)]!,
      relSig([]),
    )
  }
  return builder.build()
}

function injections<S extends string, T extends string>(
  sources: readonly S[],
  targets: readonly T[],
  compatible: (source: S, target: T) => boolean,
): Map<S, T>[] {
  const results: Map<S, T>[] = []
  const current = new Map<S, T>()
  const used = new Set<T>()
  const visit = (index: number): void => {
    if (index === sources.length) {
      results.push(new Map(current))
      return
    }
    const source = sources[index]!
    for (const target of targets) {
      if (used.has(target) || !compatible(source, target)) continue
      used.add(target)
      current.set(source, target)
      visit(index + 1)
      current.delete(source)
      used.delete(target)
    }
  }
  visit(0)
  return results
}

function directChildren(diagram: Diagram, region: RegionId): RegionId[] {
  return Object.entries(diagram.regions)
    .filter(([, candidate]) =>
      candidate.kind === 'cut' && candidate.parent === region,
    )
    .map(([id]) => id)
}

function directNodes(diagram: Diagram, region: RegionId): NodeId[] {
  return Object.entries(diagram.nodes)
    .filter(([, node]) => node.region === region)
    .map(([id]) => id)
}

/**
 * Independent full injection enumeration for the random closed ref/cut
 * corpus. It shares no production candidate construction or recursion.
 */
function bruteFootprints(
  host: Diagram,
  pattern: Diagram,
  atRegion: RegionId,
): Set<string> {
  const patternRegions = Object.keys(pattern.regions)
    .filter((region) => region !== pattern.root)
  const hostRegions = Object.keys(host.regions)
    .filter((region) => region !== host.root)
  const footprints = new Set<string>()

  for (const partialRegionMap of injections(
    patternRegions,
    hostRegions,
    () => true,
  )) {
    const regionMap = new Map(partialRegionMap)
    regionMap.set(pattern.root, atRegion)
    let regionsAgree = true
    for (const patternRegion of patternRegions) {
      const source = pattern.regions[patternRegion]!
      const hostRegion = regionMap.get(patternRegion)!
      const target = host.regions[hostRegion]!
      if (
        source.kind !== 'cut'
        || target.kind !== 'cut'
        || target.parent !== regionMap.get(source.parent)
        || directChildren(pattern, patternRegion).length
          !== directChildren(host, hostRegion).length
        || directNodes(pattern, patternRegion).length
          !== directNodes(host, hostRegion).length
      ) {
        regionsAgree = false
        break
      }
    }
    if (!regionsAgree) continue

    const patternNodes = Object.keys(pattern.nodes)
    const hostNodes = Object.keys(host.nodes)
    for (const nodeMap of injections(
      patternNodes,
      hostNodes,
      (patternNode, hostNode) => {
        const source = pattern.nodes[patternNode]!
        const target = host.nodes[hostNode]!
        return source.kind === 'ref'
          && target.kind === 'ref'
          && source.defId === target.defId
          && target.region === regionMap.get(source.region)
      },
    )) {
      footprints.add(JSON.stringify([
        [...regionMap.values()].sort(),
        [...nodeMap.values()].sort(),
        [],
        [],
      ]))
    }
  }
  return footprints
}

function matcherFootprints(
  host: Diagram,
  pattern: Diagram,
  atRegion: RegionId,
): Set<string> {
  const result = findOccurrences(
    host,
    mkDiagramWithBoundary(pattern, []),
    { inRegion: atRegion },
  )
  return new Set(result.matches.map((match) => JSON.stringify([
    [...match.regionMap.values()].sort(),
    [...match.nodeMap.values()].sort(),
    [...match.wireMap.values()].sort(),
    [...match.attachments],
  ])))
}

describe('exploration matcher independent exhaustive oracle', () => {
  it('matches full injection enumeration across deterministic random closed graphs', () => {
    const rng = mulberry32(0x1234abcd)
    for (let index = 0; index < 120; index++) {
      const host = randomClosed(rng)
      const pattern = randomClosed(rng)
      expect(
        [...matcherFootprints(host, pattern, host.root)].sort(),
        `case ${index}: matcher and independent footprints differ`,
      ).toEqual([...bruteFootprints(host, pattern, host.root)].sort())
    }
  })
})
