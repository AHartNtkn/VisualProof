import type { Diagram, RegionId } from '../../kernel/diagram/diagram'
import { mkDiagramWithBoundary, type DiagramWithBoundary } from '../../kernel/diagram/boundary'
import { findOccurrences, type Occurrence } from '../../kernel/diagram/subgraph/match'
import { occurrenceToSelection } from '../../kernel/diagram/subgraph/occurrence'
import { applyArtifactAction, type ArtifactAction } from '../artifact'
import type { PuzzleDefinition } from '../types'
import type { Hit } from '../../interaction/hittest'

export type ArtifactDropTarget = {
  readonly hit: Hit | null
  readonly containingRegion: RegionId | null
}

export type ArtifactDropRefusalCode =
  | 'artifact-incomplete'
  | 'invalid-drop-target'
  | 'no-legal-artifact-operation'

export type ArtifactDropPlan =
  | {
      readonly ok: true
      readonly operation: 'dissolve' | 'manifest'
      readonly action: ArtifactAction
    }
  | {
      readonly ok: false
      readonly code: ArtifactDropRefusalCode
      readonly reason: string
    }

export type ArtifactDropRequest = {
  readonly artifact: PuzzleDefinition
  readonly available: boolean
  readonly diagram: Diagram
  readonly target: ArtifactDropTarget
  readonly fuel: number
}

const occurrenceContains = (
  occurrence: Occurrence,
  hit: Hit,
  pattern: DiagramWithBoundary,
): boolean => {
  switch (hit.kind) {
    case 'node': return [...occurrence.nodeMap.values()].includes(hit.id)
    case 'wire': return [...occurrence.wireMap.values()].includes(hit.id)
    case 'region': return [...occurrence.regionMap]
      .some(([patternRegion, hostRegion]) =>
        pattern.diagram.regions[patternRegion]?.kind !== 'sheet' && hostRegion === hit.id)
  }
}

const occurrenceKey = (occurrence: Occurrence): string => JSON.stringify([
  occurrence.region,
  [...occurrence.regionMap.values()].sort(),
  [...occurrence.nodeMap.values()].sort(),
  [...occurrence.wireMap.values()].sort(),
  [...occurrence.attachments],
])

const refusal = (code: ArtifactDropRefusalCode, reason: string): ArtifactDropPlan => ({
  ok: false,
  code,
  reason,
})

const validates = (
  diagram: Diagram,
  action: ArtifactAction,
  artifact: PuzzleDefinition,
): boolean => {
  try {
    applyArtifactAction(diagram, action, artifact)
    return true
  } catch {
    return false
  }
}

/**
 * Plan one artifact rewrite without changing the game session. Exact occurrence
 * matching is kernel-owned; the drop pointer merely selects one returned host
 * footprint. A wrong content hit therefore cannot degrade into an insertion.
 */
export function planArtifactDrop(request: ArtifactDropRequest): ArtifactDropPlan {
  const { artifact, available, diagram, target, fuel } = request
  if (target.containingRegion === null || diagram.regions[target.containingRegion] === undefined) {
    return refusal('invalid-drop-target', 'the dropped artifact is outside the active seal')
  }
  if (!available) {
    return refusal('artifact-incomplete', 'only completed artifact records can alter a seal')
  }
  const pattern = mkDiagramWithBoundary(artifact.diagram, [])

  let occurrences: readonly Occurrence[]
  try {
    occurrences = findOccurrences(diagram, pattern, { fuel, mode: 'exact' }).matches
  } catch (error) {
    return refusal(
      'no-legal-artifact-operation',
      error instanceof Error ? error.message : String(error),
    )
  }

  if (target.hit !== null) {
    const selected = occurrences
      .filter((occurrence) => occurrenceContains(occurrence, target.hit!, pattern))
      .sort((a, b) => occurrenceKey(a).localeCompare(occurrenceKey(b)))[0]
    if (selected !== undefined) {
      const action: ArtifactAction = {
        kind: 'artifactDissolve',
        artifact: artifact.id,
        selection: occurrenceToSelection(diagram, pattern, selected),
      }
      if (validates(diagram, action, artifact)) return { ok: true, operation: 'dissolve', action }
    }
  }

  const hitAllowsManifest = target.hit === null
    || (target.hit.kind === 'region' && target.hit.id === target.containingRegion)
  if (hitAllowsManifest) {
    const action: ArtifactAction = {
      kind: 'artifactManifest',
      artifact: artifact.id,
      region: target.containingRegion,
    }
    if (validates(diagram, action, artifact)) return { ok: true, operation: 'manifest', action }
  }

  return refusal(
    'no-legal-artifact-operation',
    'that record neither exactly matches the pointed seal nor belongs in this field',
  )
}
