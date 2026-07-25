import type { Diagram, NodeId, RegionId, WireId } from '../diagram/diagram'
import { isAncestorOrEqual } from '../diagram/regions'
import { sigEquals, sigKey } from '../diagram/sig'
import type { SubgraphSelection } from '../diagram/subgraph/selection'
import { selectionContents } from '../diagram/subgraph/selection'
import { extractSubgraph } from '../diagram/subgraph/extract'
import { removeSubgraph, spliceSubgraphMapped } from '../diagram/subgraph/splice'
import type { IdReservation } from '../diagram/subgraph/freshId'
import { findOccurrences, type Occurrence } from '../diagram/subgraph/match'
import type { OccurrenceCertificate } from '../diagram/subgraph/occurrence-certificate'
import { checkOccurrenceCertificate } from '../diagram/subgraph/occurrence-certificate'
import { occurrenceToSelection } from '../diagram/subgraph/occurrence'
import { RuleError } from './error'

export type IdentityRetarget = {
  readonly boundary: number
  readonly identity: NodeId
  readonly from: WireId
  readonly to: WireId
}

type RetargetDirection = 'iteration' | 'deiteration'

/**
 * Validate every field of endpoint-level equality evidence and return the
 * attachment vector appropriate to the other side of the rule.
 *
 * Evidence is always oriented outer justifier (`from`) to inner copy (`to`).
 * Iteration therefore consumes `from` attachments and produces `to`;
 * deiteration observes `to` on the copy and reconstructs `from` for its
 * justifying occurrence.
 */
function retargetAttachments(
  diagram: Diagram,
  attachments: readonly WireId[],
  copyRegion: RegionId,
  retargets: readonly IdentityRetarget[],
  direction: RetargetDirection,
): readonly WireId[] {
  const result = [...attachments]
  const seen = new Set<number>()
  for (const retarget of retargets) {
    if (
      !Number.isSafeInteger(retarget.boundary)
      || retarget.boundary < 0
      || retarget.boundary >= attachments.length
    ) {
      throw new RuleError(
        `identity retarget boundary '${retarget.boundary}' must be a safe boundary index `
        + `below ${attachments.length}`,
      )
    }
    if (seen.has(retarget.boundary)) {
      throw new RuleError(`duplicate retarget boundary '${retarget.boundary}'`)
    }
    seen.add(retarget.boundary)

    const expected = direction === 'iteration' ? retarget.from : retarget.to
    if (attachments[retarget.boundary] !== expected) {
      const side = direction === 'iteration' ? 'source' : 'copy'
      throw new RuleError(
        `identity retarget boundary '${retarget.boundary}' ${side} attachment `
        + `'${attachments[retarget.boundary]}' does not equal '${expected}'`,
      )
    }
    if (retarget.from === retarget.to) {
      throw new RuleError('identity retarget source and target wires must be distinct')
    }

    const identity = diagram.nodes[retarget.identity]
    if (identity === undefined || identity.kind !== 'identity') {
      throw new RuleError(
        `identity retarget evidence '${retarget.identity}' does not name an identity node`,
      )
    }
    const fromWire = diagram.wires[retarget.from]
    const toWire = diagram.wires[retarget.to]
    if (fromWire === undefined) {
      throw new RuleError(`identity retarget source wire '${retarget.from}' does not exist`)
    }
    if (toWire === undefined) {
      throw new RuleError(`identity retarget target wire '${retarget.to}' does not exist`)
    }
    if (
      !sigEquals(fromWire.sig, identity.sig)
      || !sigEquals(toWire.sig, identity.sig)
    ) {
      throw new RuleError(
        `identity retarget wire signature must equal identity '${retarget.identity}' `
        + `signature '${sigKey(identity.sig)}'`,
      )
    }

    const incidences = new Set(
      Object.entries(diagram.wires)
        .filter(([, wire]) =>
          wire.endpoints.some((endpoint) => endpoint.node === retarget.identity))
        .map(([wireId]) => wireId),
    )
    if (!incidences.has(retarget.from) || !incidences.has(retarget.to)) {
      throw new RuleError(
        `identity '${retarget.identity}' does not contain both retarget wires `
        + `'${retarget.from}' and '${retarget.to}'`,
      )
    }
    if (!isAncestorOrEqual(diagram, identity.region, copyRegion)) {
      throw new RuleError(
        `identity '${retarget.identity}' in '${identity.region}' does not dominate `
        + `copy region '${copyRegion}'`,
      )
    }

    result[retarget.boundary] = direction === 'iteration'
      ? retarget.to
      : retarget.from
  }
  return Object.freeze(result)
}

/**
 * Rule 5 extends ordinary iteration: copy a subgraph into its own region or a
 * descendant not inside the copy. Named boundary positions may be retargeted
 * through dominating identities; all other positions preserve their exact
 * attachments.
 */
export function applyIteration(
  diagram: Diagram,
  selection: SubgraphSelection,
  targetRegion: RegionId,
  retargets: readonly IdentityRetarget[] = [],
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
  const mappedAttachments = retargetAttachments(
    diagram,
    attachments,
    targetRegion,
    retargets,
    'iteration',
  )
  return spliceSubgraphMapped(
    diagram,
    targetRegion,
    pattern,
    mappedAttachments,
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
  retargets: readonly IdentityRetarget[],
): { readonly contents: ReturnType<typeof selectionContents> } {
  const contents = selectionContents(diagram, selection)
  const { pattern, attachments } = extractSubgraph(diagram, selection)
  const expectedJustifierAttachments = retargetAttachments(
    diagram,
    attachments,
    selection.region,
    retargets,
    'deiteration',
  )
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
    certificate.attachments.length !== expectedJustifierAttachments.length
    || certificate.attachments.some(
      (wire, index) => wire !== expectedJustifierAttachments[index],
    )
  ) {
    throw new RuleError(
      'deiteration justifier does not preserve the identity-retargeted ordered attachments',
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
  retargets: readonly IdentityRetarget[] = [],
): DeiterationEvidence {
  const contents = selectionContents(diagram, selection)
  const { pattern, attachments } = extractSubgraph(diagram, selection)
  const justifierAttachments = retargetAttachments(
    diagram,
    attachments,
    selection.region,
    retargets,
    'deiteration',
  )
  const result = findOccurrences(diagram, pattern, {
    explorationFuel,
    attachments: justifierAttachments,
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
    occurrence.attachments.length === justifierAttachments.length
    && occurrence.attachments.every(
      (wire, index) => wire === justifierAttachments[index],
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
  evidenceGate(diagram, selection, justifier, justifying, retargets)
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
  retargets: readonly IdentityRetarget[] = [],
): Diagram {
  evidenceGate(diagram, selection, justifier, certificate, retargets)
  return removeSubgraph(diagram, selection)
}
