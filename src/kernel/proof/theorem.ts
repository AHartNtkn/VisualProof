import type { Diagram, WireId } from '../diagram/diagram'
import { polarity } from '../diagram/regions'
import type { DiagramWithBoundary } from '../diagram/boundary'
import type { SubgraphSelection } from '../diagram/subgraph/selection'
import { extractSubgraph } from '../diagram/subgraph/extract'
import { removeSubgraph, spliceSubgraphMapped } from '../diagram/subgraph/splice'
import type { IdReservation } from '../diagram/subgraph/freshId'
import { exploreForm } from '../diagram/canonical/explore'
import { RuleError } from '../rules/error'
import type { ProofContext } from './step'
import type { ProofAction } from './action'
import { replayActions } from './action'
import { ProofError } from './error'

export type Theorem = {
  readonly name: string
  readonly lhs: DiagramWithBoundary
  readonly rhs: DiagramWithBoundary
  /** Forward-oriented actions, replayed from the lhs. */
  readonly actions: readonly ProofAction[]
  /** Backward-oriented actions, replayed from the RHS with the flipped gates
      (the calculus's cut symmetry: each backward move S→S′ asserts S′ ⟹ S,
      so a chain from the rhs composes to lhs ⟹ rhs). A backward-proved
      theorem is recorded EXACTLY as the user derived it — no inverse steps
      are ever constructed. Absent = the all-forward classic form. */
  readonly backActions?: readonly ProofAction[]
}

export type TheoremApplication = {
  readonly sel: SubgraphSelection
  readonly args: readonly WireId[]
}

/**
 * Verify a theorem once: replay its steps from lhs.diagram (each applier
 * enforcing its own gate) and require the result, pinned by the lhs boundary,
 * to be isomorphic to the stated rhs respecting boundary order. Boundary
 * wires must survive the proof (keep them as the OUTER wire of any join) and
 * must be root-scoped on both sides (splice's stub invariant).
 *
 * Survival is checked after EVERY step, not just at the end: a destroyed
 * boundary id could otherwise be resurrected by a later splice's fresh-id
 * choice, certifying a false theorem through a semantically unrelated wire.
 * Per-step presence suffices because no single applier both deletes a wire
 * and mints fresh wire ids — applyTheorem, the one applier that removes and
 * splices, splices FIRST so its fresh ids avoid the entire pre-removal set.
 */
export function checkTheorem(thm: Theorem, ctx: ProofContext): void {
  if (thm.lhs.boundary.length !== thm.rhs.boundary.length) {
    throw new ProofError(
      `theorem '${thm.name}': boundary arity mismatch (lhs ${thm.lhs.boundary.length}, rhs ${thm.rhs.boundary.length})`,
    )
  }
  for (const side of [thm.lhs, thm.rhs]) {
    for (const w of side.boundary) {
      if (side.diagram.wires[w]!.scope !== side.diagram.root) {
        throw new ProofError(`theorem '${thm.name}': boundary wire '${w}' is not scoped at the diagram root`)
      }
    }
  }
  const backActions = thm.backActions ?? []
  const survival = (boundary: readonly WireId[]) => (d: Diagram, actionIndex: number, stepIndex: number): void => {
    for (const w of boundary) {
      if (d.wires[w] === undefined) {
        throw new ProofError(
          `theorem '${thm.name}': boundary wire '${w}' was destroyed by the proof (action ${actionIndex}, step ${stepIndex})`,
        )
      }
    }
  }
  const fwd = replayActions(thm.lhs.diagram, thm.actions, ctx, survival(thm.lhs.boundary))
  // the backward half replays from the RHS with flipped gates — each step
  // asserts its result entails its input, so the chain runs rhs-ward
  const bwd = replayActions(thm.rhs.diagram, backActions, ctx, survival(thm.rhs.boundary), 'backward')
  if (exploreForm(fwd, thm.lhs.boundary) !== exploreForm(bwd, thm.rhs.boundary)) {
    throw new ProofError(backActions.length === 0
      ? `theorem '${thm.name}': the proof does not arrive at the stated right-hand side`
      : `theorem '${thm.name}': the forward and backward halves do not meet`)
  }
}

/**
 * The derived-rule application (justify once, apply natively — the stored
 * proof is NEVER inlined): rewrite a verified occurrence of one theorem side
 * into the other. Forward (lhs→rhs) is sound at POSITIVE regions, reverse
 * (rhs→lhs) at NEGATIVE regions, by monotonicity. The occurrence is checked
 * exactly — extract, reorder its boundary by args, compare pinned
 * fingerprints — the same machinery as comprehension abstraction.
 */
export function applyTheorem(
  d: Diagram,
  thm: Theorem,
  at: TheoremApplication,
  direction: 'forward' | 'reverse',
  orientation: 'forward' | 'backward' = 'forward',
  reservation?: IdReservation,
): Diagram {
  const from = direction === 'forward' ? thm.lhs : thm.rhs
  const to = direction === 'forward' ? thm.rhs : thm.lhs
  // direction ties to sign; the backward orientation (reasoning from a goal)
  // flips the gate — reverse-citing on a goal's positive region is the
  // forward citation read right-to-left
  const need = (direction === 'forward') === (orientation === 'forward') ? 'positive' : 'negative'
  const have = polarity(d, at.sel.region)
  if (have !== need) {
    throw new RuleError(
      `theorem '${thm.name}' applied ${direction}${orientation === 'backward' ? ' (backward)' : ''} requires a ${need} region; '${at.sel.region}' is ${have}`,
    )
  }
  const { pattern, attachments, binderStubs } = extractSubgraph(d, at.sel)
  if (binderStubs.length > 0) {
    throw new RuleError(
      `theorem '${thm.name}' cannot be applied at an occurrence with atoms bound outside it (open theorem sides are not supported)`,
    )
  }
  if (at.args.length !== from.boundary.length) {
    throw new RuleError(
      `theorem '${thm.name}' has ${from.boundary.length} boundary positions but ${at.args.length} arguments were given`,
    )
  }
  for (const attachment of attachments) {
    if (!at.args.includes(attachment)) {
      throw new RuleError(`attachment wire '${attachment}' is not used by any theorem argument position`)
    }
  }
  // Positional arguments may repeat only when the theorem side has the same
  // intrinsic boundary alias. Repeating an argument for two distinct theorem
  // identities changes the pinned incidence form and is refused by this exact
  // comparison; theorem-call diagonalization is deliberately not inferred.
  const reordered = at.args.map((a) => {
    const j = attachments.indexOf(a)
    if (j === -1) throw new RuleError(`argument wire '${a}' is not an attachment wire of the selection`)
    return pattern.boundary[j]!
  })
  if (exploreForm(pattern.diagram, reordered) !== exploreForm(from.diagram, from.boundary)) {
    throw new RuleError(
      `the selection is not an occurrence of theorem '${thm.name}' ${direction === 'forward' ? 'left' : 'right'}-hand side`,
    )
  }
  // Splice BEFORE removing: fresh ids are then minted against the FULL
  // pre-removal id set, so this step can never resurrect an id it destroys
  // (checkTheorem's per-step boundary checks rely on exactly that). The two
  // phases commute — the splice only adds content and extends the attachment
  // wires, none of which the removal selection touches.
  const spliced = spliceSubgraphMapped(d, at.sel.region, to, at.args, { reserved: reservation }).diagram
  return removeSubgraph(spliced, at.sel)
}
