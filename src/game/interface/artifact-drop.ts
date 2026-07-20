import type { Diagram, RegionId } from '../../kernel/diagram/diagram'
import type { DiagramWithBoundary } from '../../kernel/diagram/boundary'
import { findOccurrences, occurrenceSelection, type Occurrence } from '../../kernel/diagram/subgraph/match'
import { mkSelection } from '../../kernel/diagram/subgraph/selection'
import { applyStep, type ProofContext, type ProofStep } from '../../kernel/proof/step'
import type { PuzzleDefinition } from '../types'
import { artifactTheoremName } from '../artifact-theorem'
import type { Hit } from './loupe/hittest'

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
      readonly step: Extract<ProofStep, { readonly rule: 'theorem' }>
    }
  | {
      readonly ok: false
      readonly code: ArtifactDropRefusalCode
      readonly reason: string
    }

export type ArtifactDropRequest = {
  readonly artifact: PuzzleDefinition
  readonly diagram: Diagram
  readonly context: ProofContext
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

const validates = (diagram: Diagram, step: ProofStep, context: ProofContext): boolean => {
  try {
    applyStep(diagram, step, context, 'backward')
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
  const { artifact, diagram, context, target, fuel } = request
  if (target.containingRegion === null || diagram.regions[target.containingRegion] === undefined) {
    return refusal('invalid-drop-target', 'the dropped artifact is outside the active seal')
  }
  const name = artifactTheoremName(artifact.id)
  const theorem = context.theorems.get(name)
  if (theorem === undefined) {
    return refusal('artifact-incomplete', 'only completed artifact records can alter a seal')
  }

  let occurrences: readonly Occurrence[]
  try {
    occurrences = findOccurrences(diagram, theorem.rhs, { fuel, mode: 'exact' }).matches
  } catch (error) {
    return refusal(
      'no-legal-artifact-operation',
      error instanceof Error ? error.message : String(error),
    )
  }

  if (target.hit !== null) {
    const selected = occurrences
      .filter((occurrence) => occurrenceContains(occurrence, target.hit!, theorem.rhs))
      .sort((a, b) => occurrenceKey(a).localeCompare(occurrenceKey(b)))[0]
    if (selected !== undefined) {
      const step: Extract<ProofStep, { readonly rule: 'theorem' }> = {
        rule: 'theorem',
        name,
        direction: 'reverse',
        at: {
          sel: occurrenceSelection(theorem.rhs, selected, diagram),
          args: [...selected.attachments],
        },
      }
      if (validates(diagram, step, context)) return { ok: true, operation: 'dissolve', step }
    }
  }

  const hitAllowsManifest = target.hit === null
    || (target.hit.kind === 'region' && target.hit.id === target.containingRegion)
  if (hitAllowsManifest) {
    const step: Extract<ProofStep, { readonly rule: 'theorem' }> = {
      rule: 'theorem',
      name,
      direction: 'forward',
      at: {
        sel: mkSelection(diagram, {
          region: target.containingRegion,
          regions: [],
          nodes: [],
          wires: [],
        }),
        args: [],
      },
    }
    if (validates(diagram, step, context)) return { ok: true, operation: 'manifest', step }
  }

  return refusal(
    'no-legal-artifact-operation',
    'that record neither exactly matches the pointed seal nor belongs in this field',
  )
}
