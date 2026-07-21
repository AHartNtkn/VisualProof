import type { Diagram, RegionId } from '../../kernel/diagram/diagram'
import type { DiagramWithBoundary } from '../../kernel/diagram/boundary'
import { polarity } from '../../kernel/diagram/regions'
import { mkSelection } from '../../kernel/diagram/subgraph/selection'
import { findOccurrences, type Occurrence } from '../../kernel/diagram/subgraph/match'
import { occurrenceToSelection } from '../../kernel/diagram/subgraph/occurrence'
import type { ProofContext } from '../../kernel/proof/context'
import { assertProofContext } from '../../kernel/proof/context'
import type { ProofStep } from '../../kernel/proof/step'
import type { Hit } from '../../interaction/hittest'
import type { ProofOrientation } from './moves'

export type CitationCandidate = {
  readonly name: string
  readonly direction: 'forward' | 'reverse'
  readonly from: DiagramWithBoundary
  /** Null denotes a closed side, insertable without an occurrence seam. */
  readonly occurrences: readonly Occurrence[] | null
}

export function citationDirection(
  d: Diagram,
  region: RegionId,
  orientation: ProofOrientation,
): 'forward' | 'reverse' {
  return (polarity(d, region) === 'positive') !== (orientation === 'backward') ? 'forward' : 'reverse'
}

function theoremSide(ctx: ProofContext, name: string, direction: 'forward' | 'reverse'): DiagramWithBoundary {
  const theorem = ctx.theorems.get(name)
  if (theorem === undefined) throw new Error(`unknown theorem '${name}'`)
  return direction === 'forward' ? theorem.lhs : theorem.rhs
}

function isClosed(side: DiagramWithBoundary): boolean {
  return side.boundary.length === 0
    && Object.keys(side.diagram.nodes).length === 0
    && Object.keys(side.diagram.wires).length === 0
}

function containsHits(occurrence: Occurrence, hits: readonly Hit[]): boolean {
  const nodes = new Set(occurrence.nodeMap.values())
  const wires = new Set(occurrence.wireMap.values())
  const regions = new Set(occurrence.regionMap.values())
  return hits.every((hit) => hit.kind === 'node'
    ? nodes.has(hit.id)
    : hit.kind === 'wire'
      ? wires.has(hit.id)
      : regions.has(hit.id))
}

export function citationCandidates(
  d: Diagram,
  hits: readonly Hit[],
  region: RegionId,
  ctx: ProofContext,
  orientation: ProofOrientation,
  fuel: number,
): { readonly applicable: readonly CitationCandidate[]; readonly closed: readonly CitationCandidate[] } {
  assertProofContext(ctx)
  const direction = citationDirection(d, region, orientation)
  const applicable: CitationCandidate[] = []
  const closed: CitationCandidate[] = []
  for (const [name] of ctx.theorems) {
    const from = theoremSide(ctx, name, direction)
    if (isClosed(from)) {
      closed.push({ name, direction, from, occurrences: null })
      continue
    }
    const occurrences = findOccurrences(d, from, { fuel, mode: 'exact' }).matches
      .filter((occurrence) => containsHits(occurrence, hits))
    if (occurrences.length > 0) applicable.push({ name, direction, from, occurrences })
  }
  return { applicable, closed }
}

export function citationStep(
  d: Diagram,
  candidate: CitationCandidate,
  occurrenceIndex?: number,
  region?: RegionId,
): ProofStep {
  if (candidate.occurrences === null) {
    if (region === undefined) throw new Error(`closed citation '${candidate.name}' requires a target region`)
    return {
      rule: 'theorem',
      name: candidate.name,
      direction: candidate.direction,
      at: { sel: mkSelection(d, { region, regions: [], nodes: [], wires: [] }), args: [] },
    }
  }
  if (occurrenceIndex === undefined) throw new Error(`citation '${candidate.name}' requires an occurrence`)
  const occurrence = candidate.occurrences[occurrenceIndex]
  if (occurrence === undefined) throw new Error(`citation '${candidate.name}' has no occurrence ${occurrenceIndex}`)
  return {
    rule: 'theorem',
    name: candidate.name,
    direction: candidate.direction,
    at: {
      sel: occurrenceToSelection(d, candidate.from, occurrence),
      args: [...occurrence.attachments],
    },
  }
}
