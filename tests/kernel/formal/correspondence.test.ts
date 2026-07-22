import { spawnSync } from 'node:child_process'
import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { findOccurrences } from '../../../src/kernel/diagram/subgraph/match'
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

// nestedExactness and openBinderIdentity (bubble/binder-shaped matcher
// scenarios) are dropped here, pending Plan 2 (the Lean rearchitecture to
// the same sig-indexed model — docs/superpowers/specs/
// 2026-07-22-signature-indexed-wires-design.md). There is no TS-side
// successor to reconstruct against yet: a sig-model atom always requires a
// wired head port that the old bubble/binder model didn't need, so these
// two scenarios' Lean-emitted fixtures (shaped by the old model) can never
// match a TS reconstruction until the Lean side re-emits them in the
// sig-indexed model. Correspondence coverage for these shapes is
// re-established once that lands.

// Bubble/binder-shaped fixtures with no TS-side successor yet (see the
// comment above); excluded by name, not by a runtime/environment check —
// the Lean emitter still produces them until Plan 2 lands.
const PENDING_LEAN_REARCHITECTURE = new Set(['nestedExactness', 'openBinderIdentity'])

describe('Lean/TypeScript exact matcher correspondence', () => {
  for (const fixture of emittedFixtures()) {
    if (PENDING_LEAN_REARCHITECTURE.has(fixture.fixture)) continue
    it(fixture.fixture, () => {
      switch (fixture.fixture) {
        case 'boundaryAliasesBareWire': {
          const result = runBoundaryAliasesBareWire(fixture)
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
        default:
          throw new Error(`TypeScript has no reconstruction for Lean fixture '${fixture.fixture}'`)
      }
    })
  }
})
