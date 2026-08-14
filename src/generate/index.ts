import type { Diagram } from '../kernel/diagram/diagram'
import { propShrinkFamily } from './prop/family'
import { propWalkFamily } from './walk/family'

export type KnobSpec = {
  readonly id: string
  readonly label: string
  /** 'count' knobs are free-form integers (see `min` below); 'flag' knobs
   *  hold 0/1 and render as a checkbox. */
  readonly kind: 'count' | 'flag'
  /** Validity lower bound for 'count' knobs — values below are meaningless,
   *  not merely inadvisable. There are deliberately no maxima (spec
   *  decision). Ignored for 'flag' knobs (fixed at {0,1} instead). */
  readonly min: number
  readonly default: number
}

export type GeneratedProblem = {
  readonly diagram: Diagram
  readonly statement: string
  /** Family B only: recorded action count of the certifying derivation. */
  readonly walkUpperBound?: number
}

export type GeneratorFamily = {
  readonly id: string
  readonly label: string
  readonly description: string
  readonly knobs: readonly KnobSpec[]
  generate(params: Readonly<Record<string, number>>, rng: () => number): GeneratedProblem
}

/** Fill defaults, then validate every knob: 'count' knobs must be an
 *  integer ≥ min; 'flag' knobs must be exactly 0 or 1. Unknown keys are an
 *  error — a typo must fail loudly, not silently fall to a default. */
export function readKnobs(
  family: GeneratorFamily,
  params: Readonly<Record<string, number>>,
): Record<string, number> {
  const known = new Set(family.knobs.map((knob) => knob.id))
  for (const key of Object.keys(params)) {
    if (!known.has(key)) throw new Error(`unknown knob '${key}' for family '${family.id}'`)
  }
  const values: Record<string, number> = {}
  for (const knob of family.knobs) {
    const value = params[knob.id] ?? knob.default
    if (knob.kind === 'flag') {
      if (value !== 0 && value !== 1) throw new Error(`knob '${knob.id}' is a flag and must be 0 or 1, got ${value}`)
      values[knob.id] = value
      continue
    }
    if (!Number.isInteger(value)) throw new Error(`knob '${knob.id}' must be an integer, got ${value}`)
    if (value < knob.min) throw new Error(`knob '${knob.id}' must be ≥ ${knob.min}, got ${value}`)
    values[knob.id] = value
  }
  return values
}

export const GENERATOR_FAMILIES: readonly GeneratorFamily[] = [propShrinkFamily, propWalkFamily]
