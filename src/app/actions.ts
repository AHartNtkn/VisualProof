import type { Diagram, WireId } from '../kernel/diagram/diagram'
import { polarity, wireVisibleAt } from '../kernel/diagram/regions'
import { sigEquals } from '../kernel/diagram/sig'
import { isPinEndpoint } from '../kernel/rules/wire-ends'
import type { SubgraphSelection } from '../kernel/diagram/subgraph/selection'
import type { ProofContext } from '../kernel/proof/context'
import { assertProofContext } from '../kernel/proof/context'

/**
 * Pure, read-only enumeration of moves the UI may offer for a selection.
 * Gates are MIRRORED here (never invoked): the applier remains the sole
 * authority at commit time, and its refusal message is surfaced verbatim.
 * Two-phase moves (targets and fold arguments) are flagged, not resolved.
 */
export type ActionDescriptor =
  | { readonly kind: 'erase'; readonly label: string }
  | { readonly kind: 'doubleCutWrap'; readonly label: string }
  | { readonly kind: 'doubleCutElim'; readonly label: string }
  | { readonly kind: 'identityInsert'; readonly label: string }
  | { readonly kind: 'vacuityDelete'; readonly label: string }
  | { readonly kind: 'iterate'; readonly label: string; readonly needsTarget: true }
  | { readonly kind: 'deiterate'; readonly label: string }
  | { readonly kind: 'relUnfold'; readonly label: string }
  | { readonly kind: 'relFold'; readonly label: string; readonly needsInput: 'relation' }
  | { readonly kind: 'citeTheorem'; readonly label: string; readonly name: string; readonly direction: 'forward' | 'reverse' }

/**
 * `backward` changes citation direction, flips identity insertion's polarity
 * gate, and suppresses forward-only erasure. Other structural rule gates retain
 * their physical polarity when their appliers have no orientation dual.
 */
export function applicableActions(d: Diagram, sel: SubgraphSelection, ctx: ProofContext, backward = false): ActionDescriptor[] {
  assertProofContext(ctx)
  const out: ActionDescriptor[] = []
  const pol = polarity(d, sel.region)
  const hasContent = sel.nodes.length + sel.regions.length + sel.wires.length > 0

  if (!backward && hasContent && pol === 'positive') {
    out.push({ kind: 'erase', label: 'Erase (positive region)' })
  }
  out.push({ kind: 'doubleCutWrap', label: 'Wrap in a double cut' })
  if (hasContent) {
    out.push({ kind: 'iterate', label: 'Iterate into…', needsTarget: true })
    out.push({ kind: 'deiterate', label: 'Deiterate (needs a justifying copy)' })
  }

  if (identityInsertionWires(d, sel, backward) !== null) {
    out.push({ kind: 'identityInsert', label: 'Insert identity' })
  }

  // A single reference node unfolds when its relation is in scope. Unfold is a
  // definitional equivalence (polarity-blind): no polarity gate.
  if (sel.nodes.length === 1 && sel.regions.length === 0 && sel.wires.length === 0) {
    const n = d.nodes[sel.nodes[0]!]
    if (n?.kind === 'ref' && ctx.relations.has(n.defId)) {
      out.push({ kind: 'relUnfold', label: `Unfold ${n.defId}` })
    }
  }

  // Folding replaces an occurrence of a relation body by its reference. It is
  // selection-based (the body may span nodes/regions/wires) and needs the
  // relation name; the applier's fingerprint check is the authority. Also
  // polarity-blind. Only offered when a relation exists to fold into.
  if (hasContent && ctx.relations.size > 0) {
    out.push({ kind: 'relFold', label: 'Fold into a relation…', needsInput: 'relation' })
  }

  // single selected region: structural eliminations
  if (sel.regions.length === 1 && sel.nodes.length === 0 && sel.wires.length === 0) {
    const rid = sel.regions[0]!
    const r = d.regions[rid]!
    if (r.kind === 'cut') {
      // The annulus must hold exactly one child cut and no nodes; a pin there
      // is a node and blocks, marking a quantifier that lives in the annulus.
      const children = Object.entries(d.regions).filter(([, x]) => x.kind !== 'sheet' && x.parent === rid)
      const nodesIn = Object.values(d.nodes).some((n) => n.region === rid)
      if (children.length === 1 && children[0]![1].kind === 'cut' && !nodesIn) {
        out.push({ kind: 'doubleCutElim', label: 'Eliminate the double cut' })
      }
    }
  }

  // A single bare wire — every end a pin — is ⊤-shaped whatever its
  // signature, so vacuity deletes it along with its pins. Those pins are the
  // wire's drawn ends and come with it into the selection.
  if (sel.wires.length === 1 && sel.regions.length === 0) {
    const wid = sel.wires[0]!
    const ends = d.wires[wid]!.endpoints
    if (
      ends.every((endpoint) => isPinEndpoint(d, endpoint))
      && sel.nodes.every((node) => ends.some((endpoint) => endpoint.node === node))
    ) {
      out.push({ kind: 'vacuityDelete', label: 'Delete the bare wire' })
    }
  }

  for (const [name] of ctx.theorems) {
    const direction = (pol === 'positive') !== backward ? 'forward' as const : 'reverse' as const
    out.push({ kind: 'citeTheorem', label: `Cite ${name} (${direction})`, name, direction })
  }
  return out
}

function identityInsertionWires(
  diagram: Diagram,
  selection: SubgraphSelection,
  backward: boolean,
): readonly WireId[] | null {
  const need = backward ? 'positive' : 'negative'
  // The selected wires' own pins ride along with them; anything else in the
  // selection means the gesture is not "identify these lines".
  const ownPin = (node: string): boolean => selection.wires.some((wireId) =>
    diagram.wires[wireId]?.endpoints.some((endpoint) => endpoint.node === node) === true)
  if (
    polarity(diagram, selection.region) !== need
    || !selection.nodes.every(ownPin)
    || selection.regions.length !== 0
    || selection.wires.length < 2
    || new Set(selection.wires).size !== selection.wires.length
  ) return null
  const first = diagram.wires[selection.wires[0]!]
  if (first === undefined) return null
  for (const wireId of selection.wires) {
    const wire = diagram.wires[wireId]
    if (
      wire === undefined
      || !sigEquals(first.sig, wire.sig)
      || !wireVisibleAt(diagram, wireId, selection.region)
    ) return null
  }
  return selection.wires
}
