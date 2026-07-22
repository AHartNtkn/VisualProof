import type { Diagram, RegionId, WireId } from '../diagram/diagram'
import type { DiagramWithBoundary } from '../diagram/boundary'
import { polarity } from '../diagram/regions'
import { spawnBoundRelationNode, spawnRelationNode, spawnTermNode } from '../diagram/spawn'
import type { Term } from '../term/term'
import type { IdReservation } from '../diagram/subgraph/freshId'
import { assertOpenFreePortInterface } from '../term/term'
import type { RelSig } from '../diagram/sig'
import { RuleError } from './error'

export type SpawnOrientation = 'forward' | 'backward'

function requireSpawnPolarity(d: Diagram, region: RegionId, orientation: SpawnOrientation): void {
  const need = orientation === 'forward' ? 'negative' : 'positive'
  const have = polarity(d, region)
  if (have !== need) {
    throw new RuleError(`${orientation === 'backward' ? 'backward ' : ''}spawning requires a ${need} region; '${region}' is ${have}`)
  }
}

export function applyOpenTermSpawn(
  d: Diagram,
  region: RegionId,
  term: Term,
  declaredFreePorts: readonly string[],
  orientation: SpawnOrientation = 'forward',
  reservation?: IdReservation,
): Diagram {
  requireSpawnPolarity(d, region, orientation)
  try {
    assertOpenFreePortInterface(term, declaredFreePorts)
  } catch (e) {
    throw new RuleError(`open-term spawn ${e instanceof Error ? e.message : String(e)}`)
  }
  return spawnTermNode(d, region, term, declaredFreePorts, reservation).diagram
}

export function applyRelationSpawn(
  d: Diagram,
  region: RegionId,
  defId: string,
  expectedSig: RelSig,
  relations: ReadonlyMap<string, DiagramWithBoundary>,
  orientation: SpawnOrientation = 'forward',
  reservation?: IdReservation,
): Diagram {
  requireSpawnPolarity(d, region, orientation)
  const relation = relations.get(defId)
  if (relation === undefined) throw new RuleError(`relation '${defId}' is no longer loaded`)
  if (relation.boundary.length !== expectedSig.args.length) {
    throw new RuleError(`relation '${defId}' changed arity from ${expectedSig.args.length} to ${relation.boundary.length}`)
  }
  return spawnRelationNode(d, region, defId, expectedSig, reservation).diagram
}

/**
 * Spawn a fresh atom bound to an existing relational `wire`: any relational
 * wire enclosing `region` qualifies (spawnBoundRelationNode reads the atom's
 * sig off the wire itself; mkDiagram enforces scope-encloses-region on the
 * modified wire).
 */
export function applyBoundRelationSpawn(
  d: Diagram,
  region: RegionId,
  wire: WireId,
  orientation: SpawnOrientation = 'forward',
  reservation?: IdReservation,
): Diagram {
  requireSpawnPolarity(d, region, orientation)
  return spawnBoundRelationNode(d, region, wire, reservation).diagram
}
