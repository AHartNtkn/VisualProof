import type { Diagram, WireId } from './diagram'
import { DiagramError, validateRawDiagram } from './diagram'

/**
 * A diagram plus an ordered list of boundary wires. One concept, three roles
 * (spec §2.2): rule-statement sides, exact content occurrences, and named-
 * relation definition bodies. A relation is exactly a diagram with a boundary;
 * its arity is the boundary length. Boundary entries are ordered PORT
 * INCIDENCES, not a set of wires: repeated ids mean that several boundary
 * positions expose the same line of identity.
 */
export type DiagramWithBoundary = {
  readonly diagram: Diagram
  readonly boundary: readonly WireId[]
}

/**
 * Construct the authoritative intrinsically root-open interface. Unlike an
 * ordinary closed Diagram constructor, this validates without normalizing:
 * root-co-scoped identity nodes may encode equality between distinct external
 * attachments whose scopes are unavailable until splice.
 */
export function mkDiagramWithBoundary(diagram: Diagram, boundary: readonly WireId[]): DiagramWithBoundary {
  const validated = validateRawDiagram(diagram)
  for (const w of boundary) {
    const wire = validated.wires[w]
    if (wire === undefined) throw new DiagramError(`boundary wire '${w}' does not exist`)
    if (wire.scope !== validated.root) {
      throw new DiagramError(
        `boundary wire '${w}' must be scoped at the diagram root '${validated.root}', got '${wire.scope}'`,
      )
    }
  }
  return Object.freeze({
    diagram: validated,
    boundary: Object.freeze([...boundary]),
  })
}

export function boundaryArity(d: DiagramWithBoundary): number {
  return d.boundary.length
}
