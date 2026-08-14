import type { Diagram, RegionId } from '../diagram/diagram'
import { isAncestorOrEqual } from '../diagram/regions'
import type { SubgraphSelection } from '../diagram/subgraph/selection'
import { selectionContents } from '../diagram/subgraph/selection'
import { diagramIso } from '../diagram/canonical/iso'
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
/**
 * Fast exact justifier search for single-subtree selections: testing each
 * candidate cut subtree against the pattern with pairwise isomorphism
 * (boundary-pinned) finds every exact occurrence without the matcher's
 * backtracking — which degenerates when a pattern carries many
 * interchangeable pins. The certificate is assembled from the witness
 * isomorphism.
 */
function subtreeEvidence(
  diagram: Diagram,
  selection: SubgraphSelection,
): DeiterationEvidence | null {
  if (selection.regions.length !== 1 || selection.nodes.length > 0 || selection.wires.length > 0) {
    return null
  }
  const contents = selectionContents(diagram, selection)
  const { pattern, attachments } = extractSubgraph(diagram, selection)
  for (const [rid, region] of Object.entries(diagram.regions).sort()) {
    if (region.kind !== 'cut') continue
    if (rid === selection.regions[0]) continue
    if (!isAncestorOrEqual(diagram, region.parent, selection.region)) continue
    if (contents.allRegions.has(rid)) continue
    let probe
    try {
      probe = extractSubgraph(diagram, {
        region: region.parent,
        regions: [rid],
        nodes: [],
        wires: [],
      })
    } catch {
      continue
    }
    if (probe.attachments.length !== attachments.length) continue
    if (probe.attachments.some((wire, index) => wire !== attachments[index])) continue
    const iso = diagramIso(
      pattern.diagram,
      probe.pattern.diagram,
      pattern.boundary,
      probe.pattern.boundary,
    )
    if (iso === null) continue
    // Disjointness against the selection's own content.
    const overlapping = [...iso.regions.values()].some((mapped) => contents.allRegions.has(mapped))
      || [...iso.nodes.values()].some((mapped) => contents.allNodes.has(mapped))
    if (overlapping) {
      continue
    }
    const regionMap = new Map<RegionId, RegionId>()
    for (const [from, to] of iso.regions) {
      regionMap.set(from, from === pattern.diagram.root ? region.parent : to)
    }
    const stubSet = new Set(pattern.boundary)
    const wireMap = new Map<string, string>()
    for (const [from, to] of iso.wires) {
      if (stubSet.has(from)) continue
      wireMap.set(from, to)
    }
    pattern.boundary.forEach((stub, index) => {
      if (!wireMap.has(stub)) wireMap.set(stub, probe.attachments[index]!)
    })
    const certificate: OccurrenceCertificate = {
      region: region.parent,
      regionMap,
      nodeMap: new Map(iso.nodes),
      wireMap,
      attachments: [...probe.attachments],
    }
    const justifier: SubgraphSelection = {
      region: region.parent,
      regions: [rid],
      nodes: [],
      wires: [],
    }
    const checked = checkOccurrenceCertificate(diagram, pattern, certificate)
    if (!checked.ok) continue
    return { justifier, certificate }
  }
  return null
}

export function findDeiterationEvidence(
  diagram: Diagram,
  selection: SubgraphSelection,
  explorationFuel: number,
): DeiterationEvidence {
  const fast = subtreeEvidence(diagram, selection)
  if (fast !== null) return fast
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
