import type { Diagram } from '../kernel/diagram/diagram'
import { polarity } from '../kernel/diagram/regions'
import type { SubgraphSelection } from '../kernel/diagram/subgraph/selection'
import type { ProofContext } from '../kernel/proof/step'

/**
 * Pure, read-only enumeration of moves the UI may offer for a selection.
 * Gates are MIRRORED here (never invoked): the applier remains the sole
 * authority at commit time, and its refusal message is surfaced verbatim.
 * Two-phase moves (targets, arguments, terms) are flagged, not resolved.
 */
export type ActionDescriptor =
  | { readonly kind: 'erase'; readonly label: string }
  | { readonly kind: 'insert'; readonly label: string; readonly needsInput: 'pattern' }
  | { readonly kind: 'doubleCutWrap'; readonly label: string }
  | { readonly kind: 'doubleCutElim'; readonly label: string }
  | { readonly kind: 'vacuousWrap'; readonly label: string; readonly needsInput: 'arity' }
  | { readonly kind: 'vacuousElim'; readonly label: string }
  | { readonly kind: 'iterate'; readonly label: string; readonly needsTarget: true }
  | { readonly kind: 'deiterate'; readonly label: string }
  | { readonly kind: 'instantiate'; readonly label: string; readonly needsInput: 'comprehension' }
  | { readonly kind: 'convert'; readonly label: string; readonly needsInput: 'term' }
  | { readonly kind: 'relUnfold'; readonly label: string }
  | { readonly kind: 'relFold'; readonly label: string; readonly needsInput: 'relation' }
  | { readonly kind: 'citeTheorem'; readonly label: string; readonly name: string; readonly direction: 'forward' | 'reverse' }

/**
 * `backward` is the reasoning orientation (USER ruling): the SAME move list
 * with exactly the polarity-tied gates flipped — erasure offers in negative
 * regions, insertion in positive, and citation direction ties to sign XOR
 * orientation. Everything else is direction-free and unchanged.
 */
export function applicableActions(d: Diagram, sel: SubgraphSelection, ctx: ProofContext, backward = false): ActionDescriptor[] {
  const out: ActionDescriptor[] = []
  const pol = polarity(d, sel.region)
  const eraseSign = backward ? 'negative' : 'positive'
  const hasContent = sel.nodes.length + sel.regions.length + sel.wires.length > 0

  if (hasContent && pol === eraseSign) out.push({ kind: 'erase', label: `Erase (${eraseSign} region)` })
  if (!hasContent && pol !== eraseSign) out.push({ kind: 'insert', label: 'Insert…', needsInput: 'pattern' })
  out.push({ kind: 'doubleCutWrap', label: 'Wrap in a double cut' })
  out.push({ kind: 'vacuousWrap', label: 'Wrap in a vacuous bubble…', needsInput: 'arity' })
  if (hasContent) {
    out.push({ kind: 'iterate', label: 'Iterate into…', needsTarget: true })
    out.push({ kind: 'deiterate', label: 'Deiterate (needs a justifying copy)' })
  }
  if (sel.nodes.length === 1 && sel.regions.length === 0 && d.nodes[sel.nodes[0]!]?.kind === 'term') {
    out.push({ kind: 'convert', label: 'Convert (βη)…', needsInput: 'term' })
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
      const children = Object.entries(d.regions).filter(([, x]) => x.kind !== 'sheet' && x.parent === rid)
      const nodesIn = Object.values(d.nodes).some((n) => n.region === rid)
      const wiresIn = Object.values(d.wires).some((w) => w.scope === rid)
      if (children.length === 1 && children[0]![1].kind === 'cut' && !nodesIn && !wiresIn) {
        out.push({ kind: 'doubleCutElim', label: 'Eliminate the double cut' })
      }
    }
    if (r.kind === 'bubble') {
      const bound = Object.values(d.nodes).some((n) => n.kind === 'atom' && n.binder === rid)
      if (!bound) out.push({ kind: 'vacuousElim', label: 'Dissolve the vacuous bubble' })
      // instantiation's gate flips with orientation like every polarity gate
      if (bound && polarity(d, rid) === (backward ? 'positive' : 'negative')) {
        out.push({ kind: 'instantiate', label: 'Instantiate the relation…', needsInput: 'comprehension' })
      }
    }
  }

  for (const [name] of ctx.theorems) {
    const direction = (pol === 'positive') !== backward ? 'forward' as const : 'reverse' as const
    out.push({ kind: 'citeTheorem', label: `Cite ${name} (${direction})`, name, direction })
  }
  return out
}
