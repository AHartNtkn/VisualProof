import type { PropFormula } from './formula'
import { formulaToDiagram } from '../../formula'
import { readKnobs, type GeneratedProblem, type GeneratorFamily } from '../index'
import {
  connectiveCount,
  containsDoubleNegation,
  containsDuplicateConjunct,
  isTautology,
  printTheorem,
  usedAtoms,
} from './formula'
import { samplePropFormula } from './sample'
import { containsDeiterationRedex, shrinkToCore } from './shrink'

/** Renormalize atom indices to be 0..used.length-1 in sorted order. */
function normalizeAtoms(formula: PropFormula): PropFormula {
  const usedSet = usedAtoms(formula)
  const used: number[] = [...usedSet].sort((a, b) => a - b)
  if (used.length === 0) return formula

  const mapping = new Map<number, number>()
  for (let i = 0; i < used.length; i++) {
    const atomIndex = used[i]
    if (atomIndex !== undefined) {
      mapping.set(atomIndex, i)
    }
  }

  const remap = (node: PropFormula): PropFormula => {
    switch (node.kind) {
      case 'atom': {
        const newIndex = mapping.get(node.index)
        return { kind: 'atom', index: newIndex !== undefined ? newIndex : node.index }
      }
      case 'top':
      case 'bot':
        return node
      case 'not':
        return { kind: 'not', body: remap(node.body) }
      case 'and':
        return { kind: 'and', left: remap(node.left), right: remap(node.right) }
    }
  }

  return remap(formula)
}

export const propShrinkFamily: GeneratorFamily = {
  id: 'prop-shrink',
  label: 'Random tautology (shrunk)',
  description: 'Samples random ¬/∧ formulas, keeps tautologies, and shrinks away every irrelevant part.',
  knobs: [
    { id: 'atoms', label: 'Atoms', kind: 'count', min: 1, default: 3 },
    { id: 'sampleSize', label: 'Sample connectives', kind: 'count', min: 1, default: 12 },
    { id: 'minSize', label: 'Minimum core connectives', kind: 'count', min: 1, default: 6 },
    { id: 'attempts', label: 'Attempt cap', kind: 'count', min: 1, default: 10_000 },
    // Opt-in, default off (user ruling) — measured basis: normalizeToFixpoint's
    // fixed points are nearly unsamplable (100% collapse to ⊤ across 18 knob
    // configurations, atoms 2-4, sample sizes 10-800; see shrinkToCore's
    // docstring). With it off, shrinking still repairs ¬¬ and same-area
    // duplicates (always-on, via `simplify`) but not ancestor-justified
    // redexes like Peirce's law's free opening deiteration.
    { id: 'fullDeiteration', label: 'Full deiteration normalization', kind: 'flag', min: 0, default: 0 },
  ],
  generate(params, rng): GeneratedProblem {
    const knobs = readKnobs(propShrinkFamily, params)
    const fullDeiteration = knobs.fullDeiteration === 1
    for (let attempt = 0; attempt < knobs.attempts!; attempt += 1) {
      const sampled = samplePropFormula(knobs.sampleSize!, knobs.atoms!, rng)
      if (!isTautology(sampled, knobs.atoms!)) continue
      const core = shrinkToCore(sampled, knobs.atoms!, fullDeiteration)
      if (connectiveCount(core) < knobs.minSize!) continue
      if (containsDoubleNegation(core)) {
        throw new Error(
          'prop-shrink: shrinker emitted a doubled negation — the ¬¬ collapse in simplify is broken',
        )
      }
      // Backstop covers exactly the active rewrites' redexes: flag off,
      // shrinkToCore never runs normalizeToFixpoint, so it only guarantees
      // the same-area case (`containsDuplicateConjunct`); flag on, it
      // guarantees the full ancestor-justified case
      // (`containsDeiterationRedex`). Either way, a core reaching this line
      // already cleared the size floor above, so it can never be the
      // degenerate ⊤ a full collapse produces (⊤'s connectiveCount is 0 <
      // any knob-valid minSize) — a surviving redex here means
      // shrinkToCore's loop is broken, not a legitimate outcome.
      const redexSurvived = fullDeiteration ? containsDeiterationRedex(core) : containsDuplicateConjunct(core)
      if (redexSurvived) {
        throw new Error(
          'prop-shrink: shrinker emitted a deiteration redex — the shrinkToCore fixpoint loop is broken',
        )
      }
      const normalized = normalizeAtoms(core)
      const statement = printTheorem(normalized)
      return { diagram: formulaToDiagram(statement), statement }
    }
    throw new Error(
      `prop-shrink: no core of ≥ ${knobs.minSize} connectives found in ${knobs.attempts} attempts; `
      + `lower 'Minimum core connectives' or raise 'Sample connectives' / 'Attempt cap'`,
    )
  },
}
