import type { Diagram } from '../../kernel/diagram/diagram'
import { sameDiagram } from '../../kernel/diagram'
import { applyStep, EMPTY_PROOF_CONTEXT, ProofError, type ProofStep } from '../../kernel/proof'
import { RuleError } from '../../kernel/rules'
import { enumerateMoves, type CandidateMove, type MoveClass } from '../moves'
import { diagramDigest } from './digest'

export type SearchOutcome =
  | {
      readonly status: 'solved'
      /** Which alphabet the minimum is over: phase 1 (deletions only) or
       *  phase 2 (the full atomic alphabet). */
      readonly mode: 'deletion-only' | 'full'
      /** Move count — one user gesture each. `steps.length` may exceed
       *  this: a bare-wire vacuity move contributes its whole primitive
       *  sequence to one move. */
      readonly length: number
      /** Classes proven to appear in every minimal-length proof. */
      readonly requires: readonly MoveClass[]
      readonly steps: readonly ProofStep[]
    }
  | {
      /** Phase 1 proved no deletion-only proof exists (every proof needs at
       *  least one growing move — spawn, double-cut intro, iteration copy,
       *  or vacuity insert), and phase 2's fuel ran out before solving or
       *  exhausting the full alphabet. `noProofWithin` is the deepest FULLY
       *  exhausted depth over the full alphabet: the honest claim is "no
       *  proof of ≤ noProofWithin moves exists". This does NOT by itself
       *  prove any specific class (e.g. insertion) is required — only that
       *  no deletion-only proof exists. */
      readonly status: 'exhausted'
      readonly noDeletionOnlyProof: true
      readonly noProofWithin: number
    }

/** Default phase-2 expanded-state budget. Phase 1 needs no fuel — its
 *  alphabet strictly shrinks the diagram — so this only bounds insertion
 *  search. The full alphabet's branching factor (~30, growing with the
 *  diagram as insertion moves add structure) makes exhausting even a
 *  shallow depth expensive: measured against Peirce's law
 *  (∀P Q:o. ¬(¬(¬(P∧¬Q)∧¬P)∧¬P), the spec's classic insertion-requiring
 *  case), fuel 250 exhausted depths 0-2 in 1.6s and fuel 350 in 2.2s,
 *  neither reaching depth 3 — so 300 keeps a phase-2 run in the ~1-2s
 *  range this constant is sized for, comfortably inside the ordinary
 *  suite's 5s per-test timeout. Raise or lower it by the same measurement;
 *  a 5s-budget test elsewhere in tests/generate/search.test.ts is what
 *  actually enforces the ceiling. */
export const DEFAULT_SEARCH_FUEL = 300

const ALL_CLASSES: ReadonlySet<MoveClass> = new Set(['erasure', 'spawn', 'doubleCut', 'iteration', 'vacuity'])

const DELETION_RULES = new Set(['erasure', 'deiteration', 'doubleCutElim'])

function isDeletionMove(candidate: CandidateMove): boolean {
  const first = candidate.steps[0]!
  if (DELETION_RULES.has(first.rule)) return true
  // A bare-wire deletion sequence may open with an anchoring pin insert;
  // its FINAL step (the point deletion) names its direction.
  const last = candidate.steps[candidate.steps.length - 1]!
  return last.rule === 'vacuity' && last.direction === 'delete'
}

/** Phase-1 invariant guard: every deletion move strictly shrinks the
 *  diagram, so the reachable space is finite and small. Reaching this many
 *  states means that invariant broke — a bug, so crash loudly. */
const DELETION_STATE_GUARD = 1_000_000

class FuelExhausted extends Error {
  constructor() {
    super('minimal-proof search: fuel exhausted')
  }
}

function isBlank(diagram: Diagram): boolean {
  return Object.keys(diagram.regions).length === 1
    && Object.keys(diagram.nodes).length === 0
    && Object.keys(diagram.wires).length === 0
}

type MemoEntry = { readonly diagram: Diagram; bestRemaining: number }

class DiagramMemo {
  readonly #buckets = new Map<string, MemoEntry[]>()

  /** True if an isomorphic diagram was already visited with at least as much
   *  remaining depth; otherwise records this visit. Exact, never
   *  hash-optimistic: bucket membership is confirmed by sameDiagram. */
  visitedAtLeast(diagram: Diagram, remaining: number): boolean {
    const digest = diagramDigest(diagram)
    let bucket = this.#buckets.get(digest)
    if (bucket === undefined) {
      bucket = []
      this.#buckets.set(digest, bucket)
    }
    for (const entry of bucket) {
      if (sameDiagram(entry.diagram, diagram)) {
        if (entry.bestRemaining >= remaining) return true
        entry.bestRemaining = remaining
        return false
      }
    }
    bucket.push({ diagram, bestRemaining: remaining })
    return false
  }
}

/**
 * Apply a candidate's step sequence; a rule/proof refusal withdraws it (the
 * enumerator mirrors gates, the applier is the authority); anything else
 * is a genuine bug and propagates. Erasure and deiteration cap stranded
 * wires themselves (completion pins inside the rule), so a candidate never
 * needs rescue steps: the sequence applies as enumerated or not at all.
 */
export function applyCandidateSteps(
  diagram: Diagram,
  candidateSteps: readonly ProofStep[],
): { readonly diagram: Diagram; readonly steps: readonly ProofStep[] } | null {
  let current = diagram
  for (const step of candidateSteps) {
    try {
      current = applyStep(current, step, EMPTY_PROOF_CONTEXT, 'backward')
    } catch (error) {
      if (error instanceof RuleError || error instanceof ProofError) return null
      throw error
    }
  }
  return { diagram: current, steps: candidateSteps }
}

/** Phase-1 result: `steps` is the full replayable trail; `moves` is the
 *  move count `length` reports. */
type DeletionResult = { readonly steps: readonly ProofStep[]; readonly moves: number }

/**
 * Phase 1: complete BFS over the deletion-only alphabet. Returns a minimal
 * step sequence, or null when the entire (finite) space is exhausted —
 * which PROVES no deletion-only proof exists. `excluded` removes one move
 * class for the requirement probes.
 */
function deletionSearch(start: Diagram, excluded: MoveClass | null): DeletionResult | null {
  const memo = new DiagramMemo()
  memo.visitedAtLeast(start, 0)
  let frontier: { diagram: Diagram; path: readonly ProofStep[]; moves: number }[] =
    [{ diagram: start, path: [], moves: 0 }]
  let states = 1
  while (frontier.length > 0) {
    const next: typeof frontier = []
    for (const { diagram, path, moves } of frontier) {
      if (isBlank(diagram)) return { steps: path, moves }
      for (const candidate of enumerateMoves(diagram, 'backward', ALL_CLASSES)) {
        if (!isDeletionMove(candidate)) continue
        if (excluded !== null && candidate.moveClass === excluded) continue
        const applied = applyCandidateSteps(diagram, candidate.steps)
        if (applied === null) continue
        if (memo.visitedAtLeast(applied.diagram, 0)) continue
        states += 1
        if (states > DELETION_STATE_GUARD) {
          throw new Error('deletionSearch: state guard exceeded — the strictly-shrinking invariant is broken')
        }
        next.push({ diagram: applied.diagram, path: [...path, ...applied.steps], moves: moves + 1 })
      }
    }
    frontier = next
  }
  return null
}

type Budget = { remaining: number }

function dfs(
  diagram: Diagram,
  remaining: number,
  classes: ReadonlySet<MoveClass>,
  memo: DiagramMemo,
  budget: Budget,
  trail: ProofStep[],
): boolean {
  if (isBlank(diagram)) return true
  if (remaining === 0) return false
  if (memo.visitedAtLeast(diagram, remaining)) return false
  if (budget.remaining <= 0) throw new FuelExhausted()
  budget.remaining -= 1
  for (const candidate of enumerateMoves(diagram, 'backward', classes)) {
    const applied = applyCandidateSteps(diagram, candidate.steps)
    if (applied === null) continue
    trail.push(...applied.steps)
    if (dfs(applied.diagram, remaining - 1, classes, memo, budget, trail)) return true
    trail.length -= applied.steps.length
  }
  return false
}

function solveAtDepth(
  start: Diagram,
  depth: number,
  classes: ReadonlySet<MoveClass>,
  budget: Budget,
): ProofStep[] | null {
  const trail: ProofStep[] = []
  return dfs(start, depth, classes, new DiagramMemo(), budget, trail) ? trail : null
}

export function minimalProofSearch(start: Diagram, fuel: number): SearchOutcome {
  if (!Number.isInteger(fuel) || fuel < 1) throw new Error(`minimalProofSearch: bad fuel ${fuel}`)

  // Phase 1: complete deletion-only search.
  const deletionResult = deletionSearch(start, null)
  if (deletionResult !== null) {
    const requires: MoveClass[] = []
    for (const probe of ['iteration', 'doubleCut'] as const) {
      const without = deletionSearch(start, probe)
      // No proof at all — or none as short as the minimum — without the
      // class means every minimal proof uses it.
      if (without === null || without.moves > deletionResult.moves) requires.push(probe)
    }
    return {
      status: 'solved',
      mode: 'deletion-only',
      length: deletionResult.moves,
      requires,
      steps: deletionResult.steps,
    }
  }

  // Phase 2: no deletion-only proof exists (proven); full alphabet under fuel.
  const budget: Budget = { remaining: fuel }
  for (let depth = 0; ; depth += 1) {
    let steps: ProofStep[] | null
    try {
      steps = solveAtDepth(start, depth, ALL_CLASSES, budget)
    } catch (error) {
      if (error instanceof FuelExhausted) {
        return { status: 'exhausted', noDeletionOnlyProof: true, noProofWithin: depth - 1 }
      }
      throw error
    }
    if (steps === null) continue
    const requires: MoveClass[] = []
    for (const excluded of ['spawn', 'iteration', 'doubleCut'] as const) {
      const reduced = new Set(ALL_CLASSES)
      reduced.delete(excluded)
      try {
        // Fresh budget per requirement probe: the probe is depth-capped at
        // the found length, so it is strictly smaller than the main search.
        if (solveAtDepth(start, depth, reduced, { remaining: fuel }) === null) requires.push(excluded)
      } catch (error) {
        // Probe exhausted: the requirement is UNPROVEN — omit it (the
        // `requires` list only ever contains proven requirements).
        if (!(error instanceof FuelExhausted)) throw error
      }
    }
    return { status: 'solved', mode: 'full', length: depth, requires, steps }
  }
}
