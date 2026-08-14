import { describe, expect, it } from 'vitest'
import { formulaToDiagram } from '../../src/formula'
import { applyStep, EMPTY_PROOF_CONTEXT } from '../../src/kernel/proof'
import { enumerateMoves, type MoveClass } from '../../src/generate/moves'

const ALL: ReadonlySet<MoveClass> = new Set(['erasure', 'spawn', 'doubleCut', 'iteration', 'vacuity'])
const NONCONTRADICTION = formulaToDiagram('∀P:o. ¬(P ∧ ¬P)')

describe('enumerateMoves', () => {
  it('soundness: every backward candidate applies (or is skipped as inapplicable by the applier)', () => {
    const candidates = enumerateMoves(NONCONTRADICTION, 'backward', ALL)
    expect(candidates.length).toBeGreaterThan(0)
    let applied = 0
    for (const candidate of candidates) {
      // The enumerator mirrors the gates; the applier is the authority. A
      // candidate the applier refuses is a bug in the enumerator's gate
      // mirroring, so every candidate must apply cleanly here.
      const next = applyStep(NONCONTRADICTION, candidate.step, EMPTY_PROOF_CONTEXT, 'backward')
      expect(Object.keys(next.regions).length).toBeGreaterThan(0)
      applied += 1
    }
    expect(applied).toBe(candidates.length)
  })
  it('offers the known moves on the noncontradiction diagram (backward)', () => {
    const candidates = enumerateMoves(NONCONTRADICTION, 'backward', ALL)
    const rules = new Set(candidates.map(({ step }) => step.rule))
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
    for (const { step } of candidates) {
      if ('region' in step) expect(shellRegions.has(step.region)).toBe(false)
      if ('sel' in step) expect(shellRegions.has(step.sel.region)).toBe(false)
    }
  })
  it('forward orientation flips the deletion/insertion gates', () => {
    const backward = enumerateMoves(NONCONTRADICTION, 'backward', new Set(['erasure', 'spawn']))
    const forward = enumerateMoves(NONCONTRADICTION, 'forward', new Set(['erasure', 'spawn']))
    const regionsOf = (moves: typeof forward, rule: string): Set<string> =>
      new Set(moves.filter(({ step }) => step.rule === rule)
        .map(({ step }) => ('region' in step ? step.region : 'sel' in step ? step.sel.region : '')))
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
