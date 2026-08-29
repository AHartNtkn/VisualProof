import type { Diagram, RegionId } from '../diagram/diagram'
import { mkDiagram } from '../diagram/diagram'
import { mkDiagramWithBoundary } from '../diagram/boundary'
import type { IdReservation } from '../diagram/subgraph/freshId'
import { ProofError } from './error'
import { rewriteTheoremOccurrence } from './theorem'

export type LibraryProposition = {
  readonly name: string
  readonly diagram: Diagram
}

const emptySheet = mkDiagramWithBoundary(mkDiagram({
  root: 'library-sheet',
  regions: { 'library-sheet': { kind: 'sheet' } },
  nodes: {},
  wires: {},
}), [])

/** A trusted closed proposition, validated once without any proof payload. */
export function libraryProposition(name: string, diagram: Diagram): LibraryProposition {
  if (name.trim().length === 0) throw new ProofError('library proposition name must not be blank')
  const closed = mkDiagramWithBoundary(diagram, [])
  return Object.freeze({ name, diagram: closed.diagram })
}

/** Cite a trusted closed proposition at either polarity through native rewrite. */
export function citeLibraryProposition(
  host: Diagram,
  proposition: LibraryProposition,
  target: RegionId,
  reservation?: IdReservation,
): Diagram {
  const targetSide = mkDiagramWithBoundary(proposition.diagram, [])
  return rewriteTheoremOccurrence(host, emptySheet, targetSide, {
    sel: { region: target, regions: [], nodes: [], wires: [] },
    args: [],
  }, reservation)
}
