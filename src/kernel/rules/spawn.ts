import type { Diagram, RegionId } from '../diagram/diagram'
import type { DiagramWithBoundary } from '../diagram/boundary'
import { isAncestorOrEqual, polarity } from '../diagram/regions'
import { spawnBoundRelationNode, spawnRelationNode, spawnTermNode } from '../diagram/spawn'
import type { Term } from '../term/term'
import { freePorts } from '../term/term'
import { RuleError } from './error'

export type SpawnOrientation = 'forward' | 'backward'

function requireSpawnPolarity(d: Diagram, region: RegionId, orientation: SpawnOrientation): void {
  const need = orientation === 'forward' ? 'negative' : 'positive'
  const have = polarity(d, region)
  if (have !== need) {
    throw new RuleError(`${orientation === 'backward' ? 'backward ' : ''}spawning requires a ${need} region; '${region}' is ${have}`)
  }
}

export function applyOpenTermSpawn(d: Diagram, region: RegionId, term: Term, orientation: SpawnOrientation = 'forward'): Diagram {
  requireSpawnPolarity(d, region, orientation)
  if (freePorts(term).length === 0) {
    throw new RuleError('open-term spawn requires at least one free port; use closed-term introduction')
  }
  return spawnTermNode(d, region, term).diagram
}

export function applyRelationSpawn(
  d: Diagram,
  region: RegionId,
  defId: string,
  expectedArity: number,
  relations: ReadonlyMap<string, DiagramWithBoundary>,
  orientation: SpawnOrientation = 'forward',
): Diagram {
  requireSpawnPolarity(d, region, orientation)
  const relation = relations.get(defId)
  if (relation === undefined) throw new RuleError(`relation '${defId}' is no longer loaded`)
  if (relation.boundary.length !== expectedArity) {
    throw new RuleError(`relation '${defId}' changed arity from ${expectedArity} to ${relation.boundary.length}`)
  }
  return spawnRelationNode(d, region, defId, expectedArity).diagram
}

export function applyBoundRelationSpawn(
  d: Diagram,
  region: RegionId,
  binder: RegionId,
  expectedArity: number,
  orientation: SpawnOrientation = 'forward',
): Diagram {
  requireSpawnPolarity(d, region, orientation)
  const value = d.regions[binder]
  if (value === undefined || value.kind !== 'bubble') throw new RuleError(`bound relation binder '${binder}' is not a bubble`)
  if (value.arity !== expectedArity) {
    throw new RuleError(`bound relation binder '${binder}' changed arity from ${expectedArity} to ${value.arity}`)
  }
  if (!isAncestorOrEqual(d, binder, region)) throw new RuleError(`bubble '${binder}' does not enclose spawn region '${region}'`)
  return spawnBoundRelationNode(d, region, binder).diagram
}
