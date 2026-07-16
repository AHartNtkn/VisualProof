import { spawnSync } from 'node:child_process'
import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { findOccurrences } from '../../../src/kernel/diagram/subgraph/match'
import { extractSubgraph } from '../../../src/kernel/diagram/subgraph/extract'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { parseTerm } from '../../../src/kernel/term/parse'
import type { Diagram } from '../../../src/kernel/diagram/diagram'
import type { OccurrenceCertificate } from '../../../src/kernel/diagram/subgraph/occurrence-certificate'

type Footprint = readonly [readonly number[], readonly number[], readonly number[], readonly number[]]
type Fixture = {
  readonly fixture: string
  readonly status: 'complete' | 'exhausted'
  readonly attachments: readonly number[]
  readonly found: readonly Footprint[]
}

function emittedFixtures(): readonly Fixture[] {
  const result = spawnSync('lake', ['exe', 'visualproof_match_fixtures'], {
    cwd: process.cwd(),
    encoding: 'utf8',
  })
  if (result.status !== 0) {
    throw new Error(`Lean matcher fixture emitter failed\n${result.stdout}${result.stderr}`)
  }
  return result.stdout.split(/\r?\n/).map(line => line.trim())
    .filter(line => line.startsWith('{') && line.endsWith('}'))
    .map(line => JSON.parse(line) as Fixture)
}

function ordinals(values: readonly string[]): ReadonlyMap<string, number> {
  return new Map([...values].sort().map((value, index) => [value, index]))
}

function footprint(host: Diagram, occurrence: OccurrenceCertificate): Footprint {
  const region = ordinals(Object.keys(host.regions))
  const node = ordinals(Object.keys(host.nodes))
  const wire = ordinals(Object.keys(host.wires))
  return [
    [...occurrence.regionMap.values()].map(value => region.get(value)!).sort((a, b) => a - b),
    [...occurrence.nodeMap.values()].map(value => node.get(value)!).sort((a, b) => a - b),
    [...occurrence.wireMap.values()].map(value => wire.get(value)!).sort((a, b) => a - b),
    occurrence.attachments.map(value => wire.get(value)!),
  ]
}

function runBoundaryAliasesBareWire(fixture: Fixture) {
  const hostBuilder = new DiagramBuilder()
  const hostWire = hostBuilder.wire(hostBuilder.root, [])
  const host = hostBuilder.build()

  const patternBuilder = new DiagramBuilder()
  const patternWire = patternBuilder.wire(patternBuilder.root, [])
  const pattern = mkDiagramWithBoundary(patternBuilder.build(),
    [patternWire, patternWire])
  const hostWireByOrdinal = Object.keys(host.wires).sort()
  const attachments = fixture.attachments.map(index => hostWireByOrdinal[index]!)
  const result = findOccurrences(host, pattern, {
    fuel: 100,
    explorationFuel: 100,
    mode: 'exact',
    attachments,
  })
  return {
    status: result.status,
    found: result.matches.map(match => footprint(host, match)),
    hostWire,
  }
}

function runNestedExactness() {
  const builder = new DiagramBuilder()
  const bubble = builder.bubble(builder.root, 1)
  const cut = builder.cut(bubble)
  const term = builder.termNode(cut, parseTerm('\\a. a'))
  const atom = builder.atom(cut, bubble)
  builder.wire(bubble, [
    { node: term, port: { kind: 'output' } },
    { node: atom, port: { kind: 'arg', index: 0 } },
  ])
  const host = builder.build()
  const result = findOccurrences(host, mkDiagramWithBoundary(host, []), {
    fuel: 1000,
    explorationFuel: 1000,
    mode: 'exact',
    attachments: [],
  })
  return {
    status: result.status,
    found: result.matches.map(match => footprint(host, match)),
  }
}

function runSymmetricFootprints() {
  const hostBuilder = new DiagramBuilder()
  hostBuilder.termNode(hostBuilder.root, parseTerm('\\a. a'))
  hostBuilder.termNode(hostBuilder.root, parseTerm('\\a. a'))
  const host = hostBuilder.build()

  const patternBuilder = new DiagramBuilder()
  patternBuilder.termNode(patternBuilder.root, parseTerm('\\a. a'))
  const pattern = mkDiagramWithBoundary(patternBuilder.build(), [])
  const result = findOccurrences(host, pattern, {
    fuel: 1000,
    explorationFuel: 1000,
    mode: 'exact',
    attachments: [],
  })
  return {
    status: result.status,
    found: result.matches.map(match => footprint(host, match)),
  }
}

function runOpenBinderIdentity(fixture: Fixture) {
  const builder = new DiagramBuilder()
  const outer = builder.bubble(builder.root, 1)
  const inner = builder.bubble(outer, 1)
  const cut = builder.cut(inner)
  const outerAtom = builder.atom(cut, outer)
  const innerAtom = builder.atom(cut, inner)
  builder.wire(outer, [
    { node: outerAtom, port: { kind: 'arg', index: 0 } },
  ])
  builder.wire(inner, [
    { node: innerAtom, port: { kind: 'arg', index: 0 } },
  ])
  const host = builder.build()
  const selection = mkSelection(host, {
    region: cut,
    regions: [],
    nodes: [outerAtom, innerAtom],
    wires: [],
  })
  const extracted = extractSubgraph(host, selection)
  const hostWireByOrdinal = Object.keys(host.wires).sort()
  const attachments = fixture.attachments.map(index => hostWireByOrdinal[index]!)
  const result = findOccurrences(host, extracted.pattern, {
    fuel: 1000,
    explorationFuel: 1000,
    mode: 'exact',
    attachments,
    openBinders: new Map([
      [extracted.binderStubs[0]!, outer],
      [extracted.binderStubs[1]!, inner],
    ]),
  })
  return {
    status: result.status,
    found: result.matches.map(match => footprint(host, match)),
  }
}

describe('Lean/TypeScript exact matcher correspondence', () => {
  for (const fixture of emittedFixtures()) {
    it(fixture.fixture, () => {
      switch (fixture.fixture) {
        case 'boundaryAliasesBareWire': {
          const result = runBoundaryAliasesBareWire(fixture)
          expect(result.status).toBe(fixture.status)
          expect(result.found).toEqual(fixture.found)
          break
        }
        case 'nestedExactness': {
          const result = runNestedExactness()
          expect(result.status).toBe(fixture.status)
          expect(result.found).toEqual(fixture.found)
          break
        }
        case 'symmetricFootprints': {
          const result = runSymmetricFootprints()
          expect(result.status).toBe(fixture.status)
          expect(result.found).toEqual(fixture.found)
          break
        }
        case 'openBinderIdentity': {
          const result = runOpenBinderIdentity(fixture)
          expect(result.status).toBe(fixture.status)
          expect(result.found).toEqual(fixture.found)
          break
        }
        default:
          throw new Error(`TypeScript has no reconstruction for Lean fixture '${fixture.fixture}'`)
      }
    })
  }
})
