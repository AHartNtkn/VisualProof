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
import { RuleError } from './error'

/**
 * Rule 3a (spec §3.1): copy a subgraph into its own region or any descendant
 * not inside the copy, the copy's boundary attaching to the same wires.
 * Sound everywhere — no polarity gate.
 */
export function applyIteration(d: Diagram, sel: SubgraphSelection, targetRegion: RegionId, reservation?: IdReservation): Diagram {
  const c = selectionContents(d, sel) // validates the selection loudly
  if (!isAncestorOrEqual(d, sel.region, targetRegion)) {
    throw new RuleError(`iteration target '${targetRegion}' must lie within the source region '${sel.region}'`)
  }
  if (c.allRegions.has(targetRegion)) {
    throw new RuleError(`iteration target '${targetRegion}' lies inside the iterated subgraph`)
  }
  const { pattern, attachments, binderStubs, binderAttachments } = extractSubgraph(d, sel)
  for (const hb of binderAttachments) {
    if (!isAncestorOrEqual(d, hb, targetRegion)) {
      throw new RuleError(`iteration target '${targetRegion}' lies outside binder '${hb}'; atoms cannot escape their quantifier`)
    }
  }
  const binderMap = new Map(binderStubs.map((s, i) => [s, binderAttachments[i]!]))
  return spliceSubgraphMapped(d, targetRegion, pattern, attachments, { binderMap, reserved: reservation }).diagram
}

export type DeiterationEvidence = {
  readonly justifier: SubgraphSelection
  readonly certificate: OccurrenceCertificate
}

function sameSelection(left: SubgraphSelection, right: SubgraphSelection): boolean {
  const sameIds = (a: readonly string[], b: readonly string[]): boolean =>
    a.length === b.length && [...a].sort().every((id, index) => id === [...b].sort()[index])
  return left.region === right.region
    && sameIds(left.regions, right.regions)
    && sameIds(left.nodes, right.nodes)
    && sameIds(left.wires, right.wires)
}

function evidenceGate(
  d: Diagram,
  sel: SubgraphSelection,
  justifier: SubgraphSelection,
  certificate: OccurrenceCertificate,
): { readonly contents: ReturnType<typeof selectionContents> } {
  const c = selectionContents(d, sel)
  const { pattern, attachments, binderStubs, binderAttachments } = extractSubgraph(d, sel)
  const openBinders = new Map(binderStubs.map((s, i) => [s, binderAttachments[i]!]))
  const checked = checkOccurrenceCertificate(d, pattern, certificate, { openBinders })
  if (!checked.ok) throw new RuleError(`invalid deiteration occurrence certificate: ${checked.reason}`)
  const suppliedJustifier = mkValidatedSelection(d, justifier)
  const certifiedJustifier = occurrenceToSelection(d, pattern, certificate)
  if (!sameSelection(suppliedJustifier, certifiedJustifier)) {
    throw new RuleError('deiteration justifier selection does not match its occurrence certificate')
  }
  if (!isAncestorOrEqual(d, certificate.region, sel.region)) {
    throw new RuleError(`deiteration justifier '${certificate.region}' is not an ancestor of '${sel.region}'`)
  }
  if (certificate.attachments.length !== attachments.length
    || certificate.attachments.some((wire, index) => wire !== attachments[index])) {
    throw new RuleError('deiteration justifier does not preserve the target\'s ordered attachments')
  }
  for (const region of certificate.regionMap.values()) {
    if (c.allRegions.has(region)) throw new RuleError('deiteration justifier overlaps the removed region content')
  }
  for (const node of certificate.nodeMap.values()) {
    if (c.allNodes.has(node)) throw new RuleError('deiteration justifier overlaps the removed node content')
  }
  const internal = new Set(c.internalWires)
  for (const [patternWire, hostWire] of certificate.wireMap) {
    if (pattern.boundary.includes(patternWire)) continue
    if (internal.has(hostWire)) throw new RuleError('deiteration justifier overlaps the removed wire content')
  }
  return { contents: c }
}

function mkValidatedSelection(d: Diagram, selection: SubgraphSelection): SubgraphSelection {
  // selectionContents validates the complete selection and returns no altered
  // representation; the original ordered payload remains the replay record.
  selectionContents(d, selection)
  return selection
}

/**
 * Interactive constructor for certified replay evidence. Search fuel is used
 * only here; the selected occurrence and all βη paths are returned for storage.
 */
export function findDeiterationEvidence(
  d: Diagram,
  sel: SubgraphSelection,
  fuel: number,
): DeiterationEvidence {
  const c = selectionContents(d, sel)
  const { pattern, attachments, binderStubs, binderAttachments } = extractSubgraph(d, sel)
  const openBinders = new Map(binderStubs.map((s, i) => [s, binderAttachments[i]!]))
  const { matches, undecided } = findOccurrences(d, pattern, {
    fuel,
    openBinders,
    attachments,
  })
  const disjoint = (m: Occurrence): boolean => {
    for (const r of m.regionMap.values()) if (c.allRegions.has(r)) return false
    for (const n of m.nodeMap.values()) if (c.allNodes.has(n)) return false
    const internal = new Set(c.internalWires)
    for (const [pw, hw] of m.wireMap) {
      if (pattern.boundary.includes(pw)) continue
      if (internal.has(hw)) return false
    }
    return true
  }
  const sameAttachments = (m: Occurrence): boolean =>
    m.attachments.length === attachments.length &&
    m.attachments.every((w, i) => w === attachments[i])
  const justifying = matches.find(
    (m) => isAncestorOrEqual(d, m.region, sel.region) && sameAttachments(m) && disjoint(m),
  )
  if (justifying === undefined) {
    const hint = undecided.length > 0
      ? `; ${undecided.length} node comparison(s) were undecided under fuel ${fuel} — a justification may exist beyond the fuel limit`
      : ''
    throw new RuleError(`no justifying occurrence found for deiteration at '${sel.region}'${hint}`)
  }
  const justifier = occurrenceToSelection(d, pattern, justifying)
  evidenceGate(d, sel, justifier, justifying)
  return { justifier, certificate: justifying }
}

/**
 * Rule 3b replay: validate the supplied justifying occurrence and remove the
 * selected copy. This path is deterministic, fuel-free, and performs no
 * occurrence search.
 */
export function applyDeiteration(
  d: Diagram,
  sel: SubgraphSelection,
  justifier: SubgraphSelection,
  certificate: OccurrenceCertificate,
): Diagram {
  evidenceGate(d, sel, justifier, certificate)
  return removeSubgraph(d, sel)
}
