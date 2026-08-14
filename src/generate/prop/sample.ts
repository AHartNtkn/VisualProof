import type { PropFormula } from './formula'

function rngIndex(rng: () => number, bound: number): number {
  const index = Math.floor(rng() * bound)
  if (!Number.isInteger(index) || index < 0 || index >= bound) {
    throw new Error(`rngIndex: rng produced out-of-range draw ${index} of ${bound}; rng must return [0,1)`)
  }
  return index
}

/**
 * Uniform random {¬,∧} formula with exactly `size` connectives: the root
 * connective is a fair coin between ¬ and ∧ (whenever size ≥ 1), and ∧
 * splits its remaining budget uniformly. Deliberately unbiased — quality
 * comes from the shrinker, not the sampler.
 */
export function samplePropFormula(size: number, atoms: number, rng: () => number): PropFormula {
  if (!Number.isInteger(size) || size < 0) throw new Error(`samplePropFormula: bad size ${size}`)
  if (!Number.isInteger(atoms) || atoms < 1) throw new Error(`samplePropFormula: bad atoms ${atoms}`)
  if (size === 0) return { kind: 'atom', index: rngIndex(rng, atoms) }
  if (rngIndex(rng, 2) === 0) {
    return { kind: 'not', body: samplePropFormula(size - 1, atoms, rng) }
  }
  const leftSize = rngIndex(rng, size) // 0 .. size-1; right gets the rest
  return {
    kind: 'and',
    left: samplePropFormula(leftSize, atoms, rng),
    right: samplePropFormula(size - 1 - leftSize, atoms, rng),
  }
}
