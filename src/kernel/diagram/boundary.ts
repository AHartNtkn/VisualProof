import type { Diagram, WireId } from './diagram'
import { validateRawDiagram } from './diagram'

/**
 * A diagram plus an ordered list of boundary wires. One concept, three roles
 * (spec §2.2): rule-statement sides, exact content occurrences, and named-
 * relation definition bodies. A relation is exactly a diagram with a boundary;
 * its arity is the boundary length. Boundary entries are ordered PORT
 * INCIDENCES, not a set of wires: repeated ids mean that several boundary
 * positions expose the same line of identity, and each entry counts as one
 * end of its wire at the root (so a formal exposed once needs one more end —
 * typically its root pin).
 */
export type DiagramWithBoundary = {
  readonly diagram: Diagram
  readonly boundary: readonly WireId[]
}

/**
 * Construct the authoritative intrinsically root-open interface. The
 * boundary participates in validation: entries count toward the two-end
 * floor, and a boundary wire's derived scope is the root by construction
 * (its boundary incidence lives there), so no stored-scope check exists.
 */
export function mkDiagramWithBoundary(diagram: Diagram, boundary: readonly WireId[]): DiagramWithBoundary {
  const validated = validateRawDiagram(diagram, boundary)
  return Object.freeze({
    diagram: validated,
    boundary: Object.freeze([...boundary]),
  })
}

export function boundaryArity(d: DiagramWithBoundary): number {
  return d.boundary.length
}
