import type { Diagram, RegionId } from '../../diagram/diagram'
import { polarity } from '../../diagram/regions'
import { spawnTermNode } from '../../diagram/spawn'
import type { IdReservation } from '../../diagram/subgraph/freshId'
import type { Term } from '../../term/term'
import { RuleError } from '../error'

export type LambdaSpawnOrientation = 'forward' | 'backward'

/** Spawn one whole Lambda term with a unary IOTA cap on every incidence. */
export function applyLambdaTermSpawn(
  diagram: Diagram,
  region: RegionId,
  term: Term,
  freeArity: number,
  orientation: LambdaSpawnOrientation = 'forward',
  reservation?: IdReservation,
): Diagram {
  const need = orientation === 'forward' ? 'negative' : 'positive'
  const have = polarity(diagram, region)
  if (have !== need) {
    throw new RuleError(
      `${orientation === 'backward' ? 'backward ' : ''}spawning requires a ${need} region; `
      + `'${region}' is ${have}`,
    )
  }
  return spawnTermNode(
    diagram,
    region,
    term,
    freeArity,
    reservation,
  ).diagram
}
