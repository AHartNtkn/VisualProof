import type { Diagram, RegionId, WireId } from '../diagram/diagram'
import type { DiagramWithBoundary } from '../diagram/boundary'
import { polarity } from '../diagram/regions'
import { spawnAtomNode, spawnRefNode } from '../diagram/spawn'
import type { RelSig } from '../diagram/sig'
import { sigEquals, sigKey } from '../diagram/sig'
import type { IdReservation } from '../diagram/subgraph/freshId'
import { definitionSig } from './fold'
import { RuleError } from './error'

export type SpawnOrientation = 'forward' | 'backward'

function requireSpawnPolarity(
  diagram: Diagram,
  region: RegionId,
  orientation: SpawnOrientation,
): void {
  const need = orientation === 'forward' ? 'negative' : 'positive'
  const have = polarity(diagram, region)
  if (have !== need) {
    throw new RuleError(
      `${orientation === 'backward' ? 'backward ' : ''}spawning requires a ${need} region; `
      + `'${region}' is ${have}`,
    )
  }
}

export function applyRefSpawn(
  diagram: Diagram,
  region: RegionId,
  defId: string,
  expectedSig: RelSig,
  relations: ReadonlyMap<string, DiagramWithBoundary>,
  orientation: SpawnOrientation = 'forward',
  reservation?: IdReservation,
): Diagram {
  requireSpawnPolarity(diagram, region, orientation)
  const relation = relations.get(defId)
  if (relation === undefined) throw new RuleError(`relation '${defId}' is no longer loaded`)
  const actualSig = definitionSig(relation)
  if (!sigEquals(actualSig, expectedSig)) {
    throw new RuleError(
      `relation '${defId}' changed signature from '${sigKey(expectedSig)}' `
      + `to '${sigKey(actualSig)}'`,
    )
  }
  return spawnRefNode(diagram, region, defId, expectedSig, reservation).diagram
}

export function applyAtomSpawn(
  diagram: Diagram,
  region: RegionId,
  wire: WireId,
  orientation: SpawnOrientation = 'forward',
  reservation?: IdReservation,
): Diagram {
  requireSpawnPolarity(diagram, region, orientation)
  return spawnAtomNode(diagram, region, wire, reservation).diagram
}
