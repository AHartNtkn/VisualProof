import { mkDiagramWithBoundary } from '../kernel/diagram/boundary'
import type { Diagram, RegionId } from '../kernel/diagram/diagram'
import { exploreForm } from '../kernel/diagram/canonical/explore'
import { polarity } from '../kernel/diagram/regions'
import { extractSubgraph } from '../kernel/diagram/subgraph/extract'
import type { SubgraphSelection } from '../kernel/diagram/subgraph/selection'
import { removeSubgraph, spliceSubgraph } from '../kernel/diagram/subgraph/splice'
import { GameDomainError, type PuzzleDefinition, type PuzzleId } from './types'

export type ArtifactAction =
  | {
      readonly kind: 'artifactManifest'
      readonly artifact: PuzzleId
      readonly region: RegionId
    }
  | {
      readonly kind: 'artifactDissolve'
      readonly artifact: PuzzleId
      readonly selection: SubgraphSelection
    }

export function applyArtifactAction(
  diagram: Diagram,
  action: ArtifactAction,
  artifact: PuzzleDefinition,
): Diagram {
  if (action.artifact !== artifact.id) {
    throw new GameDomainError(
      `artifact action '${action.artifact}' received catalog artifact '${artifact.id}'`,
    )
  }
  if (action.kind === 'artifactManifest') {
    if (polarity(diagram, action.region) !== 'negative') {
      throw new GameDomainError(`artifact '${artifact.id}' can manifest only in a negative region`)
    }
    return spliceSubgraph(
      diagram,
      action.region,
      mkDiagramWithBoundary(artifact.diagram, []),
      [],
    )
  }

  if (polarity(diagram, action.selection.region) !== 'positive') {
    throw new GameDomainError(`artifact '${artifact.id}' can dissolve only from a positive region`)
  }
  const extraction = extractSubgraph(diagram, action.selection)
  if (
    extraction.attachments.length !== 0
    || extraction.binderStubs.length !== 0
    || exploreForm(extraction.pattern.diagram) !== exploreForm(artifact.diagram)
  ) {
    throw new GameDomainError(
      `selection is not an exact occurrence of completed artifact '${artifact.id}'`,
    )
  }
  return removeSubgraph(diagram, action.selection)
}
