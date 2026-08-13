import type { Diagram, RegionId } from '../diagram/diagram'
import { isAncestorOrEqual } from '../diagram/regions'
import type { SubgraphSelection } from '../diagram/subgraph/selection'
import { selectionContents } from '../diagram/subgraph/selection'
import { extractSubgraph } from '../diagram/subgraph/extract'
import { removeSubgraph, spliceSubgraphMapped } from '../diagram/subgraph/splice'
import type { IdReservation } from '../diagram/subgraph/freshId'
import { findOccurrences, type Occurrence } from '../diagram/subgraph/match'
import type { OccurrenceCertificate } from '../diagram/subgraph/occurrence-certificate'
import { checkOccurrenceCertificate } from '../diagram/subgraph/occurrence-certificate'
import { occurrenceToSelection } from '../diagram/subgraph/occurrence'
import { requireRemovalScopePreserved } from './wire-ends'
import { RuleError } from './error'

/**
 * Rule 5, ordinary iteration: copy a subgraph into its own region or a
 * descendant not inside the copy; every boundary position preserves its
 * exact attachment. Substitution through an identity is a derivation
 * (iterate the identity, sever, one-point collapse), never a parameter.
 */
export function applyIteration(
  diagram: Diagram,
  selection: SubgraphSelection,
  targetRegion: RegionId,
  reservation?: IdReservation,
): Diagram {
  const contents = selectionContents(diagram, selection)
  if (!isAncestorOrEqual(diagram, selection.region, targetRegion)) {
    throw new RuleError(
      `iteration target '${targetRegion}' must lie within the source region '${selection.region}'`,
    )
  }
  if (contents.allRegions.has(targetRegion)) {
    throw new RuleError(`iteration target '${targetRegion}' lies inside the iterated subgraph`)
  }
  const { pattern, attachments } = extractSubgraph(diagram, selection)
  return spliceSubgraphMapped(
    diagram,
    targetRegion,
    pattern,
    attachments,
    { reserved: reservation },
  ).diagram
}

export type DeiterationEvidence = {
  readonly justifier: SubgraphSelection
  readonly certificate: OccurrenceCertificate
}

function sameSelection(left: SubgraphSelection, right: SubgraphSelection): boolean {
  const sameIds = (a: readonly string[], b: readonly string[]): boolean => {
    const sortedA = [...a].sort()
    const sortedB = [...b].sort()
    return sortedA.length === sortedB.length
      && sortedA.every((id, index) => id === sortedB[index])
  }
  return left.region === right.region
    && sameIds(left.regions, right.regions)
    && sameIds(left.nodes, right.nodes)
    && sameIds(left.wires, right.wires)
}

function evidenceGate(
  diagram: Diagram,
  selection: SubgraphSelection,
  justifier: SubgraphSelection,
  certificate: OccurrenceCertificate,
): { readonly contents: ReturnType<typeof selectionContents> } {
  const contents = selectionContents(diagram, selection)
  const { pattern, attachments } = extractSubgraph(diagram, selection)
  const checked = checkOccurrenceCertificate(diagram, pattern, certificate)
  if (!checked.ok) {
    throw new RuleError(`invalid deiteration occurrence certificate: ${checked.reason}`)
  }
  const suppliedJustifier = mkValidatedSelection(diagram, justifier)
  const certifiedJustifier = occurrenceToSelection(diagram, pattern, certificate)
  if (!sameSelection(suppliedJustifier, certifiedJustifier)) {
    throw new RuleError(
      'deiteration justifier selection does not match its occurrence certificate',
    )
  }
  if (!isAncestorOrEqual(diagram, certificate.region, selection.region)) {
    throw new RuleError(
      `deiteration justifier '${certificate.region}' is not an ancestor of '${selection.region}'`,
    )
  }
  if (
    certificate.attachments.length !== attachments.length
    || certificate.attachments.some(
      (wire, index) => wire !== attachments[index],
    )
  ) {
    throw new RuleError(
      'deiteration justifier does not preserve the ordered attachments',
    )
  }
  for (const region of certificate.regionMap.values()) {
    if (contents.allRegions.has(region)) {
      throw new RuleError('deiteration justifier overlaps the removed region content')
    }
  }
  for (const node of certificate.nodeMap.values()) {
    if (contents.allNodes.has(node)) {
      throw new RuleError('deiteration justifier overlaps the removed node content')
    }
  }
  const internal = new Set(contents.internalWires)
  for (const [patternWire, hostWire] of certificate.wireMap) {
    if (pattern.boundary.includes(patternWire)) continue
    if (internal.has(hostWire)) {
      throw new RuleError('deiteration justifier overlaps the removed wire content')
    }
  }
  return { contents }
}

function mkValidatedSelection(
  diagram: Diagram,
  selection: SubgraphSelection,
): SubgraphSelection {
  selectionContents(diagram, selection)
  return selection
}

/**
 * Construct exact structural replay evidence. Fuel limits graph exploration
 * only; there is no object-language comparison or secondary verdict channel.
 */
export function findDeiterationEvidence(
  diagram: Diagram,
  selection: SubgraphSelection,
  explorationFuel: number,
): DeiterationEvidence {
  const contents = selectionContents(diagram, selection)
  const { pattern, attachments } = extractSubgraph(diagram, selection)
  const result = findOccurrences(diagram, pattern, {
    explorationFuel,
    attachments,
  })
  const disjoint = (occurrence: Occurrence): boolean => {
    for (const region of occurrence.regionMap.values()) {
      if (contents.allRegions.has(region)) return false
    }
    for (const node of occurrence.nodeMap.values()) {
      if (contents.allNodes.has(node)) return false
    }
    const internal = new Set(contents.internalWires)
    for (const [patternWire, hostWire] of occurrence.wireMap) {
      if (pattern.boundary.includes(patternWire)) continue
      if (internal.has(hostWire)) return false
    }
    return true
  }
  const sameAttachments = (occurrence: Occurrence): boolean =>
    occurrence.attachments.length === attachments.length
    && occurrence.attachments.every(
      (wire, index) => wire === attachments[index],
    )
  const justifying = result.matches.find(
    (occurrence) =>
      isAncestorOrEqual(diagram, occurrence.region, selection.region)
      && sameAttachments(occurrence)
      && disjoint(occurrence),
  )
  if (justifying === undefined) {
    if (result.status === 'exhausted') {
      throw new RuleError(
        `graph exploration exhausted before finding an exact justifier `
        + `for deiteration at '${selection.region}'`,
      )
    }
    throw new RuleError(
      `no exact justifying occurrence found for deiteration at '${selection.region}'`,
    )
  }

  const justifier = occurrenceToSelection(diagram, pattern, justifying)
  evidenceGate(diagram, selection, justifier, justifying)
  return { justifier, certificate: justifying }
}

/**
 * Replay exact deiteration evidence and remove the selected inner copy.
 */
export function applyDeiteration(
  diagram: Diagram,
  selection: SubgraphSelection,
  justifier: SubgraphSelection,
  certificate: OccurrenceCertificate,
): Diagram {
  const { contents } = evidenceGate(diagram, selection, justifier, certificate)
  requireRemovalScopePreserved(
    diagram,
    contents.allNodes,
    new Set(contents.internalWires),
    'deiteration',
  )
  return removeSubgraph(diagram, selection)
}
