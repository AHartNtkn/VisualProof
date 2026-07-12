import { describe, expect, test } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { parseTerm } from '../../src/kernel/term/parse'
import {
  createOccurrenceSetState,
  cycleOccurrenceSet,
  deriveAbstractionMatches,
  deriveAbstractionSelectionState,
  maximalOccurrenceSets,
  solveMaximalOccurrenceSets,
  toggleOccurrenceExclusion,
  type AbstractionCandidate,
} from '../../src/app/abstraction-matches'

const p = (source: string) => parseTerm(source)

function unaryPattern(source = '\\x. x') {
  const builder = new DiagramBuilder()
  const node = builder.termNode(builder.root, p(source))
  const boundary = builder.wire(builder.root, [{ node, port: { kind: 'output' } }])
  return mkDiagramWithBoundary(builder.build(), [boundary])
}

function manualCandidate(
  key: string,
  footprint: { nodes?: string[]; wires?: string[]; regions?: string[] } = {},
  anchor = 'r0',
): AbstractionCandidate {
  return {
    key,
    occurrence: {
      sel: { region: anchor, regions: [], nodes: [], wires: [] },
      args: [],
    },
    footprint: {
      nodes: new Set(footprint.nodes ?? []),
      wires: new Set(footprint.wires ?? []),
      regions: new Set(footprint.regions ?? []),
    },
  }
}

describe('exact abstraction candidates', () => {
  test('returns exact occurrences inside the wrap and excludes an identical shape outside it', () => {
    const builder = new DiagramBuilder()
    const inside = builder.termNode(builder.root, p('\\x. x'))
    const insideWire = builder.wire(builder.root, [{ node: inside, port: { kind: 'output' } }])
    const outside = builder.termNode(builder.root, p('\\x. x'))
    builder.wire(builder.root, [{ node: outside, port: { kind: 'output' } }])
    const host = builder.build()
    const wrap = mkSelection(host, { region: host.root, regions: [], nodes: [inside], wires: [] })

    const result = deriveAbstractionMatches(host, wrap, unaryPattern(), { matcherFuel: 8 })

    expect(result.status).toBe('complete')
    expect(result.candidates).toHaveLength(1)
    expect(result.candidates[0]!.occurrence.sel.nodes).toEqual([inside])
    expect(result.candidates[0]!.occurrence.args).toEqual([insideWire])
  })

  test('enumerates a diagonal exact occurrence and preserves repeated argument order', () => {
    const patternBuilder = new DiagramBuilder()
    const patternNode = patternBuilder.termNode(patternBuilder.root, p('y'))
    const output = patternBuilder.wire(patternBuilder.root, [{ node: patternNode, port: { kind: 'output' } }])
    const free = patternBuilder.wire(patternBuilder.root, [{ node: patternNode, port: { kind: 'freeVar', name: 'y' } }])
    const pattern = mkDiagramWithBoundary(patternBuilder.build(), [output, free])

    const hostBuilder = new DiagramBuilder()
    const hostNode = hostBuilder.termNode(hostBuilder.root, p('y'))
    const shared = hostBuilder.wire(hostBuilder.root, [
      { node: hostNode, port: { kind: 'output' } },
      { node: hostNode, port: { kind: 'freeVar', name: 'y' } },
    ])
    const host = hostBuilder.build()
    const wrap = mkSelection(host, { region: host.root, regions: [], nodes: [hostNode], wires: [] })

    const result = deriveAbstractionMatches(host, wrap, pattern, { matcherFuel: 8 })

    expect(result.status).toBe('complete')
    expect(result.candidates).toHaveLength(1)
    expect(result.candidates[0]!.occurrence.args).toEqual([shared, shared])
    expect(result.candidates[0]!.key).toContain(JSON.stringify([shared, shared]))
  })

  test('distinguishes exhaustive zero matches from matcher exhaustion', () => {
    const simple = new DiagramBuilder()
    const unmatched = simple.termNode(simple.root, p('\\x. \\y. x'))
    const host = simple.build()
    const wrap = mkSelection(host, { region: host.root, regions: [], nodes: [unmatched], wires: [] })
    const zero = deriveAbstractionMatches(host, wrap, unaryPattern(), { matcherFuel: 1 })
    expect(zero).toMatchObject({ status: 'complete', candidates: [] })

    const nested = new DiagramBuilder()
    const cut = nested.cut(nested.root)
    nested.termNode(cut, p('\\x. \\y. x'))
    const nestedHost = nested.build()
    const nestedWrap = mkSelection(nestedHost, { region: nestedHost.root, regions: [cut], nodes: [], wires: [] })
    const exhausted = deriveAbstractionMatches(nestedHost, nestedWrap, unaryPattern(), { matcherFuel: 1 })
    expect(exhausted.status).toBe('exhausted')
  })
})

describe('deterministic maximal occurrence sets', () => {
  test('overlap is shared node, internal wire, or selected region', () => {
    const nodeA = manualCandidate('node-a', { nodes: ['n'] })
    const nodeB = manualCandidate('node-b', { nodes: ['n'] })
    const wireA = manualCandidate('wire-a', { wires: ['w'] })
    const wireB = manualCandidate('wire-b', { wires: ['w'] })
    const regionA = manualCandidate('region-a', { regions: ['r'] })
    const regionB = manualCandidate('region-b', { regions: ['r'] })

    expect(maximalOccurrenceSets([nodeA, nodeB], new Set()).map((set) => set.map(({ key }) => key))).toEqual([
      ['node-a'], ['node-b'],
    ])
    expect(maximalOccurrenceSets([wireA, wireB], new Set()).map((set) => set.map(({ key }) => key))).toEqual([
      ['wire-a'], ['wire-b'],
    ])
    expect(maximalOccurrenceSets([regionA, regionB], new Set()).map((set) => set.map(({ key }) => key))).toEqual([
      ['region-a'], ['region-b'],
    ])
  })

  test('an occurrence anchored inside another selected region is incompatible with it', () => {
    const outer = manualCandidate('outer', { regions: ['inner'] })
    const nested = manualCandidate('nested', { nodes: ['n'] }, 'inner')

    expect(maximalOccurrenceSets([outer, nested], new Set()).map((set) => set.map(({ key }) => key))).toEqual([
      ['nested'], ['outer'],
    ])
  })

  test('orders maximal sets by descending size then canonical key sequence', () => {
    const a = manualCandidate('a', { nodes: ['left'] })
    const b = manualCandidate('b', { nodes: ['left', 'right'] })
    const c = manualCandidate('c', { nodes: ['right'] })

    expect(maximalOccurrenceSets([c, b, a], new Set()).map((set) => set.map(({ key }) => key))).toEqual([
      ['a', 'c'],
      ['b'],
    ])
  })

  test('reports solver exhaustion separately and never returns partial sets as complete', () => {
    const candidates = [manualCandidate('a'), manualCandidate('b'), manualCandidate('c')]

    expect(solveMaximalOccurrenceSets(candidates, new Set(), 1)).toMatchObject({
      status: 'exhausted',
      sets: [],
    })
    expect(solveMaximalOccurrenceSets(candidates, new Set(), 100)).toMatchObject({
      status: 'complete',
      sets: [[candidates[0], candidates[1], candidates[2]]],
    })
  })

  test('cycles forward and backward through complete sets', () => {
    const a = manualCandidate('a', { nodes: ['left'] })
    const b = manualCandidate('b', { nodes: ['left', 'right'] })
    const c = manualCandidate('c', { nodes: ['right'] })
    const initial = createOccurrenceSetState([a, b, c], new Set(), 100)

    const forward = cycleOccurrenceSet(initial, 1)
    expect(forward.activeIndex).toBe(1)
    expect(forward.sets[forward.activeIndex]!.map(({ key }) => key)).toEqual(['b'])
    expect(cycleOccurrenceSet(forward, 1).activeIndex).toBe(0)
    expect(cycleOccurrenceSet(initial, -1).activeIndex).toBe(1)
  })

  test('click exclusion toggles, restores, and stale exclusions disappear with new candidates', () => {
    const a = manualCandidate('a')
    const b = manualCandidate('b')
    const initial = createOccurrenceSetState([a, b], new Set(), 100)

    const excluded = toggleOccurrenceExclusion(initial, 'a')
    expect([...excluded.excluded]).toEqual(['a'])
    expect(excluded.sets[0]!.map(({ key }) => key)).toEqual(['b'])

    const restored = toggleOccurrenceExclusion(excluded, 'a')
    expect([...restored.excluded]).toEqual([])
    expect(restored.sets[0]!.map(({ key }) => key)).toEqual(['a', 'b'])

    const draftChanged = createOccurrenceSetState([b], new Set(['a']), 100)
    expect([...draftChanged.excluded]).toEqual([])
  })
})

describe('abstraction selection state', () => {
  test('a nonempty unmatched draft disables finalize', () => {
    const builder = new DiagramBuilder()
    const hostNode = builder.termNode(builder.root, p('\\x. \\y. x'))
    const host = builder.build()
    const wrap = mkSelection(host, { region: host.root, regions: [], nodes: [hostNode], wires: [] })

    const state = deriveAbstractionSelectionState(host, wrap, unaryPattern(), {
      matcherFuel: 8,
      solverFuel: 100,
    })

    expect(state).toMatchObject({ kind: 'matches', matchStatus: 'complete', canFinalize: false })
  })

  test('an actually empty nullary draft is exactly one selected marker state', () => {
    const builder = new DiagramBuilder()
    const host = builder.build()
    const wrap = mkSelection(host, { region: host.root, regions: [], nodes: [], wires: [] })
    const empty = new DiagramBuilder()
    const pattern = mkDiagramWithBoundary(empty.build(), [])

    const state = deriveAbstractionSelectionState(host, wrap, pattern, {
      matcherFuel: 1,
      solverFuel: 1,
    })

    expect(state).toEqual({
      kind: 'empty-marker',
      anchor: host.root,
      selected: true,
      canFinalize: true,
    })
  })
})
