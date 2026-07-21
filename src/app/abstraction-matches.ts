import type { Diagram, NodeId, RegionId, WireId } from '../kernel/diagram/diagram'
import type { DiagramWithBoundary } from '../kernel/diagram/boundary'
import { findOccurrences } from '../kernel/diagram/subgraph/match'
import { occurrenceToSelection } from '../kernel/diagram/subgraph/occurrence'
import { extractSubgraph } from '../kernel/diagram/subgraph/extract'
import { selectionContents, type SubgraphSelection } from '../kernel/diagram/subgraph/selection'
import { diagonalize, type AbstractionOccurrence } from '../kernel/rules/comprehension'

export type AbstractionCandidate = {
  readonly key: string
  readonly occurrence: AbstractionOccurrence
  readonly footprint: {
    readonly nodes: ReadonlySet<NodeId>
    readonly wires: ReadonlySet<WireId>
    readonly regions: ReadonlySet<RegionId>
  }
}

export type AbstractionMatchResult =
  | { readonly status: 'complete'; readonly candidates: readonly AbstractionCandidate[] }
  | { readonly status: 'exhausted'; readonly candidates: readonly AbstractionCandidate[] }

export type MaximalOccurrenceSetResult =
  | { readonly status: 'complete'; readonly sets: readonly (readonly AbstractionCandidate[])[] }
  | { readonly status: 'exhausted'; readonly sets: readonly [] }

export type OccurrenceSetState = {
  readonly candidates: readonly AbstractionCandidate[]
  readonly excluded: ReadonlySet<string>
  readonly status: 'complete' | 'exhausted'
  readonly sets: readonly (readonly AbstractionCandidate[])[]
  readonly activeIndex: number
  readonly solverFuel: number
}

export type AbstractionSelectionState =
  | {
    readonly kind: 'matches'
    readonly matchStatus: 'complete' | 'exhausted'
    readonly occurrenceSets: OccurrenceSetState
    readonly canFinalize: boolean
  }
  | {
    readonly kind: 'empty-marker'
    readonly anchor: RegionId
    readonly selected: true
    readonly canFinalize: true
  }

function positiveFuel(value: number, name: string): void {
  if (!Number.isSafeInteger(value) || value <= 0) {
    throw new Error(`${name} must be a positive safe integer, got ${value}`)
  }
}

function sorted<T extends string>(values: Iterable<T>): T[] {
  return [...values].sort()
}

function subset<T>(values: Iterable<T>, containing: ReadonlySet<T>): boolean {
  for (const value of values) if (!containing.has(value)) return false
  return true
}

/** Lazily enumerate every quotient of ordered boundary positions once. */
function* boundaryQuotients(arity: number): Generator<readonly number[]> {
  if (arity === 0) {
    yield []
    return
  }
  const current = [0]
  function* visit(position: number, maximum: number): Generator<readonly number[]> {
    if (position === arity) {
      yield [...current]
      return
    }
    for (let next = 0; next <= maximum + 1; next++) {
      current.push(next)
      yield* visit(position + 1, Math.max(maximum, next))
      current.pop()
    }
  }
  yield* visit(1, 0)
}

/**
 * Compose call-site quotient labels with intrinsic repeated boundary-wire
 * identities, returning the effective attachment index for every authored
 * boundary position. Class numbering follows first appearance, exactly as
 * `diagonalize` orders its collapsed boundary.
 */
function effectiveBoundaryClasses(
  boundary: readonly WireId[],
  quotient: readonly number[],
): readonly number[] {
  const parent = quotient.map((_, index) => index)
  const find = (index: number): number => parent[index] === index
    ? index
    : (parent[index] = find(parent[index]!))
  const unite = (left: number, right: number): void => {
    const leftRoot = find(left)
    const rightRoot = find(right)
    if (leftRoot !== rightRoot) parent[rightRoot] = leftRoot
  }
  const firstLabel = new Map<number, number>()
  const firstWire = new Map<WireId, number>()
  for (let index = 0; index < quotient.length; index++) {
    const label = quotient[index]!
    const wire = boundary[index]!
    const labelPrior = firstLabel.get(label)
    if (labelPrior === undefined) firstLabel.set(label, index)
    else unite(labelPrior, index)
    const wirePrior = firstWire.get(wire)
    if (wirePrior === undefined) firstWire.set(wire, index)
    else unite(wirePrior, index)
  }
  const classIndex = new Map<number, number>()
  return quotient.map((_, index) => {
    const root = find(index)
    let effective = classIndex.get(root)
    if (effective === undefined) {
      effective = classIndex.size
      classIndex.set(root, effective)
    }
    return effective
  })
}

function actuallyEmptyNullary(pattern: DiagramWithBoundary): boolean {
  return pattern.boundary.length === 0
    && Object.keys(pattern.diagram.regions).length === 1
    && Object.keys(pattern.diagram.nodes).length === 0
    && Object.keys(pattern.diagram.wires).length === 0
}

function candidateKey(
  selection: SubgraphSelection,
  footprint: AbstractionCandidate['footprint'],
  args: readonly WireId[],
): string {
  return JSON.stringify([
    selection.region,
    sorted(footprint.regions),
    sorted(footprint.nodes),
    sorted(footprint.wires),
    args,
  ])
}

/**
 * Exhaustively derive exact candidates within the provisional wrap.
 *
 * Matcher fuel is shared across lazy boundary-quotient production, anchor
 * dispatch, and the matcher's internal exploration probes. Running out returns
 * `exhausted`; accumulated candidates are explicitly partial and never
 * presented as a complete result.
 */
export function deriveAbstractionMatches(
  host: Diagram,
  wrap: SubgraphSelection,
  pattern: DiagramWithBoundary,
  options: { readonly matcherFuel: number },
): AbstractionMatchResult {
  positiveFuel(options.matcherFuel, 'matcher fuel')
  const wrapContents = selectionContents(host, wrap)
  if (actuallyEmptyNullary(pattern)) return { status: 'complete', candidates: [] }

  const allowedRegions = new Set<RegionId>([wrap.region, ...wrapContents.allRegions])
  const anchors = sorted(allowedRegions)
  const wrapWires = new Set(wrapContents.internalWires)
  const byKey = new Map<string, AbstractionCandidate>()
  let remaining = options.matcherFuel

  for (const quotient of boundaryQuotients(pattern.boundary.length)) {
    if (remaining === 0) {
      return { status: 'exhausted', candidates: [...byKey.values()].sort(compareCandidate) }
    }
    remaining-- // producing this quotient is orchestration work
    const effectiveClasses = effectiveBoundaryClasses(pattern.boundary, quotient)
    const searchedPattern = diagonalize(pattern, quotient)
    for (const anchor of anchors) {
      if (remaining === 0) {
        return { status: 'exhausted', candidates: [...byKey.values()].sort(compareCandidate) }
      }
      remaining-- // dispatching this anchored search is orchestration work
      if (remaining === 0) {
        return { status: 'exhausted', candidates: [...byKey.values()].sort(compareCandidate) }
      }
      const found = findOccurrences(host, searchedPattern, {
        fuel: options.matcherFuel,
        explorationFuel: remaining,
        mode: 'exact',
        inRegion: anchor,
      })
      remaining -= found.explorationSteps
      for (const match of found.matches) {
        const selection = occurrenceToSelection(host, searchedPattern, match)
        const contents = selectionContents(host, selection)
        if (!allowedRegions.has(selection.region)
          || !subset(contents.allNodes, wrapContents.allNodes)
          || !subset(contents.allRegions, wrapContents.allRegions)
          || !subset(contents.internalWires, wrapWires)) continue

        const extraction = extractSubgraph(host, selection)
        if (extraction.binderStubs.length > 0) {
          throw new Error('subgraphs with atoms bound outside the occurrence cannot be abstracted')
        }

        const args = Object.freeze(effectiveClasses.map((boundaryClass) => match.attachments[boundaryClass]!))
        const footprint = Object.freeze({
          nodes: new Set(contents.allNodes),
          wires: new Set(contents.internalWires),
          regions: new Set(contents.allRegions),
        })
        const occurrence = Object.freeze({ sel: selection, args })
        const key = candidateKey(selection, footprint, args)
        byKey.set(key, Object.freeze({ key, occurrence, footprint }))
      }
      if (found.status === 'exhausted') {
        return { status: 'exhausted', candidates: [...byKey.values()].sort(compareCandidate) }
      }
    }
  }

  return { status: 'complete', candidates: [...byKey.values()].sort(compareCandidate) }
}

function compareCandidate(a: AbstractionCandidate, b: AbstractionCandidate): number {
  return a.key < b.key ? -1 : a.key > b.key ? 1 : 0
}

function intersects<T>(a: ReadonlySet<T>, b: ReadonlySet<T>): boolean {
  const [small, large] = a.size <= b.size ? [a, b] : [b, a]
  for (const value of small) if (large.has(value)) return true
  return false
}

function overlaps(a: AbstractionCandidate, b: AbstractionCandidate): boolean {
  return intersects(a.footprint.nodes, b.footprint.nodes)
    || intersects(a.footprint.wires, b.footprint.wires)
    || intersects(a.footprint.regions, b.footprint.regions)
    || a.footprint.regions.has(b.occurrence.sel.region)
    || b.footprint.regions.has(a.occurrence.sel.region)
}

function compareSets(a: readonly AbstractionCandidate[], b: readonly AbstractionCandidate[]): number {
  if (a.length !== b.length) return b.length - a.length
  for (let index = 0; index < a.length; index++) {
    const order = compareCandidate(a[index]!, b[index]!)
    if (order !== 0) return order
  }
  return 0
}

/** Fuel-bounded maximal-independent-set enumeration. Any exhaustion discards partial output. */
export function solveMaximalOccurrenceSets(
  candidates: readonly AbstractionCandidate[],
  excluded: ReadonlySet<string>,
  solverFuel: number,
): MaximalOccurrenceSetResult {
  positiveFuel(solverFuel, 'solver fuel')
  const unique = new Map<string, AbstractionCandidate>()
  for (const candidate of candidates) {
    if (!excluded.has(candidate.key)) unique.set(candidate.key, candidate)
  }
  const allowed = [...unique.values()].sort(compareCandidate)
  const finished = new Map<string, readonly AbstractionCandidate[]>()
  let remaining = solverFuel
  let exhausted = false

  const visit = (index: number, chosen: AbstractionCandidate[]): void => {
    if (exhausted) return
    if (remaining === 0) {
      exhausted = true
      return
    }
    remaining--
    if (index === allowed.length) {
      const maximal = allowed.every((candidate) =>
        chosen.includes(candidate) || chosen.some((selected) => overlaps(candidate, selected)))
      if (maximal) {
        const keySequence = JSON.stringify(chosen.map(({ key }) => key))
        finished.set(keySequence, Object.freeze([...chosen]))
      }
      return
    }
    const candidate = allowed[index]!
    if (chosen.every((selected) => !overlaps(candidate, selected))) {
      chosen.push(candidate)
      visit(index + 1, chosen)
      chosen.pop()
    }
    visit(index + 1, chosen)
  }

  visit(0, [])
  if (exhausted) return { status: 'exhausted', sets: [] }
  return { status: 'complete', sets: [...finished.values()].sort(compareSets) }
}

/** Convenience exhaustive enumeration with a finite safe-integer backtracking budget. */
export function maximalOccurrenceSets(
  candidates: readonly AbstractionCandidate[],
  excluded: ReadonlySet<string>,
): readonly (readonly AbstractionCandidate[])[] {
  const result = solveMaximalOccurrenceSets(candidates, excluded, Number.MAX_SAFE_INTEGER)
  if (result.status === 'exhausted') throw new Error('maximal occurrence set enumeration exhausted')
  return result.sets
}

export function createOccurrenceSetState(
  candidates: readonly AbstractionCandidate[],
  excluded: ReadonlySet<string>,
  solverFuel: number,
): OccurrenceSetState {
  const candidateKeys = new Set(candidates.map(({ key }) => key))
  const liveExcluded = new Set([...excluded].filter((key) => candidateKeys.has(key)))
  const result = solveMaximalOccurrenceSets(candidates, liveExcluded, solverFuel)
  return Object.freeze({
    candidates: Object.freeze([...candidates].sort(compareCandidate)),
    excluded: liveExcluded,
    status: result.status,
    sets: result.sets,
    activeIndex: 0,
    solverFuel,
  })
}

export function cycleOccurrenceSet(state: OccurrenceSetState, delta: 1 | -1): OccurrenceSetState {
  if (state.status === 'exhausted' || state.sets.length === 0) return state
  const activeIndex = (state.activeIndex + delta + state.sets.length) % state.sets.length
  return Object.freeze({ ...state, activeIndex })
}

export function toggleOccurrenceExclusion(state: OccurrenceSetState, key: string): OccurrenceSetState {
  if (!state.candidates.some((candidate) => candidate.key === key)) {
    throw new Error(`unknown abstraction candidate '${key}'`)
  }
  const excluded = new Set(state.excluded)
  if (excluded.has(key)) excluded.delete(key)
  else excluded.add(key)
  return createOccurrenceSetState(state.candidates, excluded, state.solverFuel)
}

export function deriveAbstractionSelectionState(
  host: Diagram,
  wrap: SubgraphSelection,
  pattern: DiagramWithBoundary,
  options: { readonly matcherFuel: number; readonly solverFuel: number; readonly excluded?: ReadonlySet<string> },
): AbstractionSelectionState {
  if (actuallyEmptyNullary(pattern)) {
    return { kind: 'empty-marker', anchor: wrap.region, selected: true, canFinalize: true }
  }
  const matches = deriveAbstractionMatches(host, wrap, pattern, options)
  const occurrenceSets = createOccurrenceSetState(
    matches.candidates,
    options.excluded ?? new Set(),
    options.solverFuel,
  )
  const active = occurrenceSets.sets[occurrenceSets.activeIndex]
  return {
    kind: 'matches',
    matchStatus: matches.status,
    occurrenceSets,
    canFinalize: matches.status === 'complete'
      && occurrenceSets.status === 'complete'
      && active !== undefined
      && active.length > 0,
  }
}
