import type { Diagram, NodeId, RegionId, WireId } from '../kernel/diagram/diagram'
import { isAncestorOrEqual, polarity } from '../kernel/diagram/regions'
import { sigEquals } from '../kernel/diagram/sig'
import type { SubgraphSelection } from '../kernel/diagram/subgraph/selection'
import type { ProofContext } from '../kernel/proof/context'
import { assertProofContext } from '../kernel/proof/context'
import type { IdentityContradictionEvidence } from '../kernel/rules/identity'

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
  | { readonly kind: 'identityContradiction'; readonly label: string }
  | { readonly kind: 'vacuousElim'; readonly label: string }
  | { readonly kind: 'iterate'; readonly label: string; readonly needsTarget: true }
  | { readonly kind: 'deiterate'; readonly label: string }
  | { readonly kind: 'relUnfold'; readonly label: string }
  | { readonly kind: 'relFold'; readonly label: string; readonly needsInput: 'relation' }
  | { readonly kind: 'citeTheorem'; readonly label: string; readonly name: string; readonly direction: 'forward' | 'reverse' }

/**
 * `backward` is the reasoning orientation (USER ruling): the SAME move list
 * with exactly the orientation-aware gates flipped. Identity insertion is
 * Rule 4 and remains tied to a physically negative region in both proof
 * orientations.
 */
export function applicableActions(d: Diagram, sel: SubgraphSelection, ctx: ProofContext, backward = false): ActionDescriptor[] {
  assertProofContext(ctx)
  const out: ActionDescriptor[] = []
  const pol = polarity(d, sel.region)
  const eraseSign = backward ? 'negative' : 'positive'
  const hasContent = sel.nodes.length + sel.regions.length + sel.wires.length > 0

  if (hasContent && pol === eraseSign) out.push({ kind: 'erase', label: `Erase (${eraseSign} region)` })
  out.push({ kind: 'doubleCutWrap', label: 'Wrap in a double cut' })
  if (hasContent) {
    out.push({ kind: 'iterate', label: 'Iterate into…', needsTarget: true })
    out.push({ kind: 'deiterate', label: 'Deiterate (needs a justifying copy)' })
  }

  if (identityInsertionWires(d, sel) !== null) {
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
      const children = Object.entries(d.regions).filter(([, x]) => x.kind !== 'sheet' && x.parent === rid)
      const nodesIn = Object.values(d.nodes).some((n) => n.region === rid)
      const wiresIn = Object.values(d.wires).some((w) => w.scope === rid)
      if (children.length === 1 && children[0]![1].kind === 'cut' && !nodesIn && !wiresIn) {
        out.push({ kind: 'doubleCutElim', label: 'Eliminate the double cut' })
      }
      if (findIdentityContradictionEvidence(d, rid) !== null) {
        out.push({ kind: 'identityContradiction', label: 'Eliminate the identity contradiction' })
      }
    }
  }

  // A single endpoint-free wire of any signature is structurally vacuous.
  if (sel.wires.length === 1 && sel.regions.length === 0 && sel.nodes.length === 0) {
    const wid = sel.wires[0]!
    const w = d.wires[wid]!
    if (w.endpoints.length === 0) out.push({ kind: 'vacuousElim', label: 'Eliminate the vacuous wire' })
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
): readonly WireId[] | null {
  if (
    polarity(diagram, selection.region) !== 'negative'
    || selection.nodes.length !== 0
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
      || !isAncestorOrEqual(diagram, wire.scope, selection.region)
    ) return null
  }
  return selection.wires
}

function incidentWires(diagram: Diagram, node: NodeId): ReadonlySet<WireId> {
  return new Set(Object.entries(diagram.wires)
    .filter(([, wire]) => wire.endpoints.some((endpoint) => endpoint.node === node))
    .map(([wire]) => wire))
}

export function findIdentityContradictionEvidence(
  diagram: Diagram,
  enclosingCut: RegionId,
): IdentityContradictionEvidence | null {
  const enclosing = diagram.regions[enclosingCut]
  if (enclosing === undefined || enclosing.kind !== 'cut') return null
  const equalities = Object.entries(diagram.nodes)
    .filter((entry): entry is [NodeId, Extract<Diagram['nodes'][NodeId], { kind: 'identity' }>] =>
      entry[1].kind === 'identity' && entry[1].region === enclosingCut)
    .sort(([left], [right]) => left.localeCompare(right))
  const childCuts = Object.entries(diagram.regions)
    .filter((entry): entry is [RegionId, Extract<Diagram['regions'][RegionId], { kind: 'cut' }>] =>
      entry[1].kind === 'cut' && entry[1].parent === enclosingCut)
    .sort(([left], [right]) => left.localeCompare(right))
  for (const [equality, equalityNode] of equalities) {
    const equalityWires = incidentWires(diagram, equality)
    for (const [disequalityCut] of childCuts) {
      const disequalities = Object.entries(diagram.nodes)
        .filter((entry): entry is [NodeId, Extract<Diagram['nodes'][NodeId], { kind: 'identity' }>] =>
          entry[1].kind === 'identity' && entry[1].region === disequalityCut)
        .sort(([left], [right]) => left.localeCompare(right))
      for (const [disequality, disequalityNode] of disequalities) {
        if (!sigEquals(equalityNode.sig, disequalityNode.sig)) continue
        const disequalityWires = incidentWires(diagram, disequality)
        if (
          equalityWires.size === disequalityWires.size
          && [...equalityWires].every((wire) => disequalityWires.has(wire))
        ) return { equality, disequalityCut, disequality }
      }
    }
  }
  return null
}
