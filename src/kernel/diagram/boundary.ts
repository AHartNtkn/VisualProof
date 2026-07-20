import type { Diagram, WireId } from './diagram'
import { DiagramError } from './diagram'

/**
 * A diagram plus an ordered list of boundary wires. One concept, three roles
 * (spec §2.2): rule-statement sides, comprehension instances, and named-
 * relation definition bodies. A relation is exactly a diagram with a boundary;
 * its arity is the boundary length. Boundary entries are ordered PORT
 * INCIDENCES, not a set of wires: repeated ids mean that several boundary
 * positions expose the same line of identity.
 */
export type DiagramWithBoundary = {
  readonly diagram: Diagram
  readonly boundary: readonly WireId[]
}

/** Construct an intrinsically root-open diagram interface. */
export function mkDiagramWithBoundary(diagram: Diagram, boundary: readonly WireId[]): DiagramWithBoundary {
  for (const w of boundary) {
    const wire = diagram.wires[w]
    if (wire === undefined) throw new DiagramError(`boundary wire '${w}' does not exist`)
    if (wire.scope !== diagram.root) {
      throw new DiagramError(
        `boundary wire '${w}' must be scoped at the diagram root '${diagram.root}', got '${wire.scope}'`,
      )
    }
  }
  return Object.freeze({ diagram, boundary: Object.freeze([...boundary]) })
}

export function boundaryArity(d: DiagramWithBoundary): number {
  return d.boundary.length
}
