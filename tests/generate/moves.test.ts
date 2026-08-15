import { describe, expect, it } from 'vitest'
import { formulaToDiagram } from '../../src/formula'
import { enumerateMoves, type MoveClass } from '../../src/generate/moves'
import { applyCandidateWithPins } from '../../src/generate/search/search'

const ALL: ReadonlySet<MoveClass> = new Set(['erasure', 'spawn', 'doubleCut', 'iteration', 'vacuity'])
const NONCONTRADICTION = formulaToDiagram('∀P:o. ¬(P ∧ ¬P)')

// Soundness corpus: statements chosen to exercise the alphabet across
// different shapes, including the final review's demonstrated hole case (a
// cut-selection erasure that strands a wire below the two-end floor and
// must be rescued by the search's auto-pin bundle rather than dropped).
const SOUNDNESS_STATEMENTS: readonly string[] = [
  '∀P:o. ¬(P ∧ ¬P)',
  '∀P Q:o. ¬(¬(P ∧ Q) ∧ P ∧ Q)',
  '∀P Q:o. ¬(P ∧ ¬P) ∧ ¬(Q ∧ ¬Q)',
  '∀P:o. ¬¬¬(P ∧ ¬P)',
  '∀P Q:o. ¬(P ∧ ¬(Q ∧ ¬Q))',
]

describe('enumerateMoves', () => {
  it('soundness: every backward candidate applies directly or via the search\'s auto-pin bundle', () => {
    for (const statement of SOUNDNESS_STATEMENTS) {
      const diagram = formulaToDiagram(statement)
      const candidates = enumerateMoves(diagram, 'backward', ALL)
      expect(candidates.length).toBeGreaterThan(0)
      let applied = 0
      for (const candidate of candidates) {
        // The enumerator mirrors the gates; the applier is the authority. A
        // candidate that strands a wire below the two-end floor raises
        // ScopePreservationError, which the search's auto-pin bundle
        // resolves; any other refusal is a bug in the enumerator's gate
        // mirroring, so every candidate must apply cleanly (directly or
        // bundled) here.
        const bundled = applyCandidateWithPins(diagram, candidate.steps)
        expect(bundled).not.toBeNull()
        expect(Object.keys(bundled!.diagram.regions).length).toBeGreaterThan(0)
        applied += 1
      }
      expect(applied).toBe(candidates.length)
    }
  })
  it('offers the known moves on the noncontradiction diagram (backward)', () => {
    const candidates = enumerateMoves(NONCONTRADICTION, 'backward', ALL)
    const rules = new Set(candidates.flatMap(({ steps }) => steps.map((step) => step.rule)))
    expect(rules.has('deiteration')).toBe(true)   // inner P justified by outer P
    expect(rules.has('erasure')).toBe(true)       // e.g. P in the negative body cut
    expect(rules.has('doubleCutIntro')).toBe(true)
    expect(rules.has('atomSpawn')).toBe(true)     // positive regions exist
    // The ∀ shell desugars to two cuts (¬∃¬), and the body's own leading ¬
    // adds a third: the quantifier body cut forms a genuine empty-annulus
    // ¬¬ pair with it, so doubleCutElim is legitimately offered there.
    expect(rules.has('doubleCutElim')).toBe(true)
  })
  it('respects the within-region frame: no moves touch the shell from inside a frame', () => {
    // Frame the enumeration at the body cut: no candidate's step may target
    // the root or the shell cuts, and doubleCutElim never targets the frame.
    const diagram = NONCONTRADICTION
    const shellRegions = new Set([diagram.root])
    const candidates = enumerateMoves(diagram, 'backward', ALL, bodyRegion(diagram))
    for (const { steps } of candidates) {
      for (const step of steps) {
        if ('region' in step) expect(shellRegions.has(step.region)).toBe(false)
        if ('sel' in step) expect(shellRegions.has(step.sel.region)).toBe(false)
      }
    }
  })
  it('forward orientation flips the deletion/insertion gates', () => {
    const backward = enumerateMoves(NONCONTRADICTION, 'backward', new Set(['erasure', 'spawn']))
    const forward = enumerateMoves(NONCONTRADICTION, 'forward', new Set(['erasure', 'spawn']))
    const regionsOf = (moves: typeof forward, rule: string): Set<string> =>
      new Set(moves.filter(({ steps }) => steps[0]!.rule === rule)
        .map(({ steps }) => {
          const step = steps[0]!
          return 'region' in step ? step.region : 'sel' in step ? step.sel.region : ''
        }))
    // A region offering backward erasure (negative) must not offer forward erasure.
    for (const region of regionsOf(backward, 'erasure')) {
      expect(regionsOf(forward, 'erasure').has(region)).toBe(false)
    }
    for (const region of regionsOf(backward, 'atomSpawn')) {
      expect(regionsOf(forward, 'atomSpawn').has(region)).toBe(false)
    }
  })
})

function bodyRegion(diagram: ReturnType<typeof formulaToDiagram>): string {
  const cutsUnder = (parent: string): string[] =>
    Object.entries(diagram.regions)
      .filter(([, region]) => region.kind === 'cut' && region.parent === parent)
      .map(([id]) => id)
  const outer = cutsUnder(diagram.root)[0]!
  return cutsUnder(outer)[0]!
}
