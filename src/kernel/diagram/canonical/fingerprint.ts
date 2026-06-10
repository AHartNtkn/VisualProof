import type { Diagram } from '../diagram'
import type { DiagramWithBoundary } from '../boundary'
import { canonicalForm } from './canonical'

/**
 * Content fingerprint: the canonical serialization itself. Exact by
 * construction — equal strings iff isomorphic diagrams. If profiling ever
 * shows fingerprint length matters for storage, hash AT THE STORAGE LAYER and
 * keep this exact string as the comparison key; never compare hashes for
 * soundness-relevant equality.
 */
export function diagramFingerprint(d: Diagram): string {
  return canonicalForm(d)
}

/** Boundary-pinned fingerprint: boundary order is significant. */
export function boundaryFingerprint(dwb: DiagramWithBoundary): string {
  return canonicalForm(dwb.diagram, dwb.boundary)
}

export function diagramsIsomorphic(d1: Diagram, d2: Diagram): boolean {
  if (
    Object.keys(d1.regions).length !== Object.keys(d2.regions).length ||
    Object.keys(d1.nodes).length !== Object.keys(d2.nodes).length ||
    Object.keys(d1.wires).length !== Object.keys(d2.wires).length
  ) {
    return false
  }
  return canonicalForm(d1) === canonicalForm(d2)
}
