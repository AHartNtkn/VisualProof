import type { Diagram, WireId } from './diagram'
import { DiagramError } from './diagram'

/**
 * A diagram plus an ordered list of boundary wires. One concept, three roles
 * (spec §2.2): rule-statement sides, comprehension instances, and named-
 * relation definition bodies. A relation is exactly a diagram with a boundary;
 * its arity is the boundary length.
 */
export type DiagramWithBoundary = {
  readonly diagram: Diagram
  readonly boundary: readonly WireId[]
}

export function mkDiagramWithBoundary(diagram: Diagram, boundary: readonly WireId[]): DiagramWithBoundary {
  const seen = new Set<WireId>()
  for (const w of boundary) {
    if (diagram.wires[w] === undefined) throw new DiagramError(`boundary wire '${w}' does not exist`)
    if (seen.has(w)) throw new DiagramError(`duplicate boundary wire '${w}'`)
    seen.add(w)
  }
  return Object.freeze({ diagram, boundary: Object.freeze([...boundary]) })
}

export function boundaryArity(d: DiagramWithBoundary): number {
  return d.boundary.length
}
