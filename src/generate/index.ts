import type { Diagram } from '../kernel/diagram/diagram'
import { propShrinkFamily } from './prop/family'
import { propWalkFamily } from './walk/family'

export type KnobSpec = {
  readonly id: string
  readonly label: string
  /** Validity lower bound — values below are meaningless, not merely
   *  inadvisable. There are deliberately no maxima (spec decision). */
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

/** Fill defaults, then validate every knob: integer and ≥ min. Unknown keys
 *  are an error — a typo must fail loudly, not silently fall to a default. */
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
    if (!Number.isInteger(value)) throw new Error(`knob '${knob.id}' must be an integer, got ${value}`)
    if (value < knob.min) throw new Error(`knob '${knob.id}' must be ≥ ${knob.min}, got ${value}`)
    values[knob.id] = value
  }
  return values
}

export const GENERATOR_FAMILIES: readonly GeneratorFamily[] = [propShrinkFamily, propWalkFamily]
