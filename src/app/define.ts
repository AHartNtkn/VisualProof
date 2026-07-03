import type { Diagram, WireId } from '../kernel/diagram/diagram'
import type { DiagramWithBoundary } from '../kernel/diagram/boundary'
import { mkDiagramWithBoundary } from '../kernel/diagram/boundary'
import type { SubgraphSelection } from '../kernel/diagram/subgraph/selection'
import { extractSubgraph } from '../kernel/diagram/subgraph/extract'
import type { ProofContext } from '../kernel/proof/step'

/**
 * Name a live selection as a new relation: the EXTRACTED COPY of the selection
 * (extractSubgraph — the same gates comprehension abstraction and relFold use)
 * with its crossing wires as the ordered boundary. Pure and headless: the input
 * diagram is never mutated (extractSubgraph copies), and the result is a
 * self-contained DiagramWithBoundary the caller registers as `name`. Registering
 * a definition is a conservative definitional extension — nothing on the sheet
 * changes when a relation is defined.
 *
 * `orderedWires` is the caller's pick order over the selection's crossing wires;
 * that order IS the argument order (boundary index i = the i-th pick), exactly
 * mirroring citation/relFold's "click the argument wires in boundary order". The
 * extracted boundary (sorted by host-wire id) is reordered to the picks, so the
 * disc's port pip renders the picked order.
 *
 * Every failure is a loud, instructive error:
 * - empty name;
 * - name collision with an existing relation (loaded or session) or a theorem
 *   (relations and theorems share one namespace so fold/cite inputs stay
 *   unambiguous);
 * - a crossing wire left unpicked, a wire picked twice, or a non-crossing wire
 *   picked;
 * - a selection that binds atoms OUTSIDE itself — an open subgraph — is refused,
 *   the same gate comprehension abstraction (comprehension.ts) and relFold apply:
 *   such a body references a variable it does not bind, so it could never be
 *   folded and is not a self-contained relation.
 */
export function defineRelation(
  diagram: Diagram,
  sel: SubgraphSelection,
  orderedWires: readonly WireId[],
  name: string,
  ctx: ProofContext,
  relations: Readonly<Record<string, DiagramWithBoundary>>,
): { relation: DiagramWithBoundary } {
  if (name.trim() === '') {
    throw new Error('relation name is empty: type a name in the name input first')
  }
  if (ctx.relations.has(name) || Object.prototype.hasOwnProperty.call(relations, name)) {
    throw new Error(`relation '${name}' already exists (loaded or defined this session); choose a fresh name`)
  }
  if (ctx.theorems.has(name)) {
    throw new Error(
      `the name '${name}' is already a theorem; relations and theorems share one namespace, so pick a different relation name`,
    )
  }

  // Non-destructive: extractSubgraph copies the selection out; `diagram` is
  // untouched.
  const { pattern, attachments, binderStubs } = extractSubgraph(diagram, sel)
  if (binderStubs.length > 0) {
    throw new Error(
      'the selection binds atoms outside itself, so it is not a self-contained relation; include the binder in the selection or pick a closed subgraph',
    )
  }

  // The picks must be exactly the crossing wires, each once: the boundary IS the
  // crossing-wire set, and the argument order is the pick order.
  const picked = new Set<WireId>()
  for (const w of orderedWires) {
    if (picked.has(w)) {
      throw new Error(`argument wire '${w}' is picked more than once; pick each crossing wire exactly once`)
    }
    if (!attachments.includes(w)) {
      throw new Error(
        `wire '${w}' is not a crossing wire of the selection; only the selection's boundary wires (${attachments.join(', ') || 'none'}) are arguments`,
      )
    }
    picked.add(w)
  }
  for (const a of attachments) {
    if (!picked.has(a)) {
      throw new Error(
        `crossing wire '${a}' was not picked; every boundary wire is an argument — pick all ${attachments.length} of them`,
      )
    }
  }

  // Reorder the extracted boundary (host-wire-id order) to the pick order, so
  // boundary index i is the i-th picked wire's stub.
  const boundary = orderedWires.map((w) => pattern.boundary[attachments.indexOf(w)]!)
  return { relation: mkDiagramWithBoundary(pattern.diagram, boundary) }
}
