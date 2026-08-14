import type { Diagram, WireId } from '../kernel/diagram/diagram'
import type { DiagramWithBoundary } from '../kernel/diagram/boundary'
import { mkDiagramWithBoundary } from '../kernel/diagram/boundary'
import type { SubgraphSelection } from '../kernel/diagram/subgraph/selection'
import { extractSubgraph } from '../kernel/diagram/subgraph/extract'
import { canonicalWireOrder } from '../kernel/diagram/canonical/wire-order'
import { findOccurrences } from '../kernel/diagram/subgraph/match'
import { occurrenceToSelection } from '../kernel/diagram/subgraph/occurrence'
import type { ProofContext } from '../kernel/proof/context'
import { assertProofContext } from '../kernel/proof/context'

/**
 * Name a live selection as a new relation: the extracted copy of the selection
 * (the same structural boundary authority used by relFold)
 * with its crossing wires as the ordered boundary. Pure and headless: the input
 * diagram is never mutated (extractSubgraph copies), and the result is a
 * self-contained DiagramWithBoundary the caller registers as `name`. Registering
 * a definition is a conservative definitional extension — nothing on the sheet
 * changes when a relation is defined.
 *
 * Every failure is a loud, instructive error:
 * - empty name;
 * - name collision with an existing relation (loaded or session) or a theorem
 *   (relations and theorems share one namespace so fold/cite inputs stay
 *   unambiguous);
 * Every crossing wire is an explicit boundary incidence; there is no separate
 * binding or closure interpretation at this layer. Boundary order is always
 * the canonical explorer order and cannot be overridden by a caller.
 */
export function defineRelation(
  diagram: Diagram,
  sel: SubgraphSelection,
  name: string,
  ctx: ProofContext,
): { relation: DiagramWithBoundary } {
  if (typeof name !== 'string') {
    throw new Error('manual boundary order is not supported; definitions use canonical boundary order')
  }
  assertProofContext(ctx)
  if (name.trim() === '') {
    throw new Error('relation name is empty: type a name in the name input first')
  }
  if (ctx.relations.has(name)) {
    throw new Error(`relation '${name}' already exists (loaded or defined this session); choose a fresh name`)
  }
  if (ctx.theorems.has(name)) {
    throw new Error(
      `the name '${name}' is already a theorem; relations and theorems share one namespace, so pick a different relation name`,
    )
  }

  // Non-destructive: extractSubgraph copies the selection out; `diagram` is
  // untouched. Crossing relational wires become higher-order boundary
  // parameters — a self-contained relation may still take relation arguments.
  const { pattern, attachments } = extractSubgraph(diagram, sel)

  const boundary = canonicalArgOrder(diagram, sel).map((wire) =>
    pattern.boundary[attachments.indexOf(wire)]!)
  return { relation: mkDiagramWithBoundary(pattern.diagram, boundary) }
}

/**
 * The canonical argument order for a selection's crossing wires: the order the
 * canonical explorer assigns to their boundary stubs in the extracted body.
 * Deterministic and id-invariant — isomorphic selections get the same order —
 * so definition authoring has one authoritative order.
 */
export function canonicalArgOrder(diagram: Diagram, sel: SubgraphSelection): WireId[] {
  const { pattern, attachments } = extractSubgraph(diagram, sel)
  const ord = canonicalWireOrder(pattern.diagram)
  return [...attachments]
    .map((host, i) => ({ host, o: ord.get(pattern.boundary[i]!)! }))
    .sort((a, b) => a.o - b.o)
    .map((x) => x.host)
}

/**
 * Infer relFold's argument wires for a selection: the definition's boundary
 * order is already fixed, so which host wire plays which argument is exactly
 * an occurrence match of the body against the selection — no user picking.
 * When the body has symmetric arguments, any valid assignment folds to the
 * same diagram, so the first (canonical) occurrence is taken. Refusal is
 * based only on exact graph matching, never a search budget: no
 * `explorationFuel` is passed, so `findOccurrences`'s `spend()` never sees
 * `remaining === 0` (an absent budget leaves `remaining` `undefined`
 * forever) and `status` is always `'complete'` — the same decisive
 * treatment `diagramIso` gives adversarial worst cases, with no fuel cap on
 * a check that must be exact.
 *
 * The search is also selection-scaled: `images` restricts every occurrence's
 * region/node/internal-wire images to `sel`'s own elements, so the matcher
 * never explores host structure outside the selection. This is sound, not a
 * heuristic — the loop below only accepts an occurrence whose image sets are
 * EXACTLY `sel`'s (the `sameIds` checks), so any occurrence `images` prunes
 * would have been rejected anyway. Without it, disconnected
 * structurally-identical decoy components elsewhere in `sel.region` leave
 * their candidate sets unsplit by content-only propagation, making the true
 * cost multiplicative in the decoy count rather than additive in element
 * count — restricting to `sel`'s own elements removes the decoys from the
 * search entirely instead of bounding a search that still considers them.
 */
export function inferFoldArgs(
  diagram: Diagram,
  sel: SubgraphSelection,
  defId: string,
  ctx: ProofContext,
): WireId[] {
  assertProofContext(ctx)
  const body = ctx.relations.get(defId)
  if (body === undefined) {
    throw new Error(`unknown relation '${defId}' (known: ${[...ctx.relations.keys()].join(', ') || 'none'})`)
  }
  const found = findOccurrences(diagram, body, {
    inRegion: sel.region,
    images: { regions: sel.regions, nodes: sel.nodes, wires: sel.wires },
  })
  const sameIds = (left: readonly string[], right: readonly string[]): boolean => {
    const a = [...left].sort()
    const b = [...right].sort()
    return a.length === b.length && a.every((id, index) => id === b[index])
  }
  for (const occ of found.matches) {
    const occurrence = occurrenceToSelection(diagram, body, occ)
    if (
      occurrence.region === sel.region
      && sameIds(occurrence.regions, sel.regions)
      && sameIds(occurrence.nodes, sel.nodes)
      && sameIds(occurrence.wires, sel.wires)
    ) return [...occ.attachments]
  }
  throw new Error(`the selection must match the definition exactly.`)
}
