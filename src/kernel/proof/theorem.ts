import type { Diagram, WireId } from '../diagram/diagram'
import { polarity } from '../diagram/regions'
import type { DiagramWithBoundary } from '../diagram/boundary'
import { mkDiagramWithBoundary } from '../diagram/boundary'
import type { SubgraphSelection } from '../diagram/subgraph/selection'
import { extractSubgraph } from '../diagram/subgraph/extract'
import { removeSubgraph, spliceSubgraph } from '../diagram/subgraph/splice'
import { boundaryFingerprint } from '../diagram/canonical/fingerprint'
import { RuleError } from '../rules/error'
import type { ProofStep, ProofContext } from './step'
import { replayProof } from './step'
import { ProofError } from './error'

export type Theorem = {
  readonly name: string
  readonly lhs: DiagramWithBoundary
  readonly rhs: DiagramWithBoundary
  readonly steps: readonly ProofStep[]
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
  const result = replayProof(thm.lhs.diagram, thm.steps, ctx, (d, i) => {
    for (const w of thm.lhs.boundary) {
      if (d.wires[w] === undefined) {
        throw new ProofError(`theorem '${thm.name}': boundary wire '${w}' was destroyed by the proof (step ${i})`)
      }
    }
  })
  const got = boundaryFingerprint(mkDiagramWithBoundary(result, thm.lhs.boundary))
  if (got !== boundaryFingerprint(thm.rhs)) {
    throw new ProofError(`theorem '${thm.name}': the proof does not arrive at the stated right-hand side`)
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
): Diagram {
  const from = direction === 'forward' ? thm.lhs : thm.rhs
  const to = direction === 'forward' ? thm.rhs : thm.lhs
  const need = direction === 'forward' ? 'positive' : 'negative'
  const have = polarity(d, at.sel.region)
  if (have !== need) {
    throw new RuleError(
      `theorem '${thm.name}' applied ${direction} requires a ${need} region; '${at.sel.region}' is ${have}`,
    )
  }
  const { pattern, attachments, binderStubs } = extractSubgraph(d, at.sel)
  if (binderStubs.length > 0) {
    throw new RuleError(
      `theorem '${thm.name}' cannot be applied at an occurrence with atoms bound outside it (open theorem sides are not supported)`,
    )
  }
  if (at.args.length !== attachments.length) {
    throw new RuleError(
      `the selection has ${attachments.length} attachment wires but theorem '${thm.name}' takes ${at.args.length} arguments here`,
    )
  }
  if (new Set(at.args).size !== at.args.length) {
    throw new RuleError(`theorem argument wires are not distinct`)
  }
  const reordered = at.args.map((a) => {
    const j = attachments.indexOf(a)
    if (j === -1) throw new RuleError(`argument wire '${a}' is not an attachment wire of the selection`)
    return pattern.boundary[j]!
  })
  if (boundaryFingerprint(mkDiagramWithBoundary(pattern.diagram, reordered)) !== boundaryFingerprint(from)) {
    throw new RuleError(
      `the selection is not an occurrence of theorem '${thm.name}' ${direction === 'forward' ? 'left' : 'right'}-hand side`,
    )
  }
  // Splice BEFORE removing: fresh ids are then minted against the FULL
  // pre-removal id set, so this step can never resurrect an id it destroys
  // (checkTheorem's per-step boundary checks rely on exactly that). The two
  // phases commute — the splice only adds content and extends the attachment
  // wires, none of which the removal selection touches.
  const spliced = spliceSubgraph(d, at.sel.region, to, at.args)
  return removeSubgraph(spliced, at.sel)
}
