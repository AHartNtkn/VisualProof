import { DiagramBuilder } from '../kernel/diagram/builder'
import type { Diagram, WireId } from '../kernel/diagram/diagram'
import { mkDiagramWithBoundary, type DiagramWithBoundary } from '../kernel/diagram/boundary'
import { relSig, sigKey, type RelSig } from '../kernel/diagram/sig'
import type { ProofContext } from '../kernel/proof/context'
import { assertProofContext } from '../kernel/proof/context'
import { applyStep, type ProofStep } from '../kernel/proof/step'

export type ProofOrientation = 'forward' | 'backward'

/** The relation signature of a named definition: its boundary stub sorts, in order. */
function relationSig(relation: DiagramWithBoundary): RelSig {
  return relSig(relation.boundary.map((wid) => {
    const w = relation.diagram.wires[wid]
    if (w === undefined) throw new Error(`relation boundary wire '${wid}' is missing from its content`)
    return w.sig
  }))
}

/** Construct the closed reference comprehension for one named relation: a single
 * `ref` node whose argument wires are the boundary. Attaching this as a body to a
 * relational wire witnesses that wire with the named relation. Named definitions
 * are closed, so the boundary is exactly the argument positions (no parameters).
 * Higher-order definitions are supported: each boundary wire carries its own sort. */
export function foldedComprehension(ctx: ProofContext, name: string): DiagramWithBoundary {
  assertProofContext(ctx)
  const relation = ctx.relations.get(name)
  if (relation === undefined) throw new Error(`unknown named relation '${name}'`)
  const sig = relationSig(relation)
  const builder = new DiagramBuilder()
  const ref = builder.ref(builder.root, name, sig)
  const boundary: WireId[] = []
  for (let index = 0; index < sig.args.length; index++) {
    boundary.push(builder.wire(builder.root, [{ node: ref, port: { kind: 'arg', index } }], sig.args[index]!))
  }
  return mkDiagramWithBoundary(builder.build(), boundary)
}

/**
 * Resolve an explicit named-relation request into a submission-ready body-attach
 * step: witnessing a relational wire with the named relation's closed
 * comprehension IS instantiation in the sig model. Named definitions never infer
 * host parameters — the definition is closed — so the target wire's arity must
 * match the definition's boundary exactly and the body carries no parameters.
 */
export function resolveNamedRelationInstantiation(
  diagram: Diagram,
  wire: WireId,
  ctx: ProofContext,
  name: string,
  orientation: ProofOrientation,
): ProofStep {
  assertProofContext(ctx)
  const relation = ctx.relations.get(name)
  if (relation === undefined) throw new Error(`unknown named relation '${name}'`)
  const target = diagram.wires[wire]
  if (target === undefined) throw new Error(`named relation instantiation target wire '${wire}' does not exist`)
  if (target.sig.kind !== 'rel') {
    throw new Error(`named relation instantiation requires a relational wire; '${wire}' has sig '${sigKey(target.sig)}'`)
  }
  const comp = foldedComprehension(ctx, name)
  if (comp.boundary.length !== target.sig.args.length) {
    throw new Error(
      `named relation arity mismatch: '${name}' has ${comp.boundary.length} boundary parameters but target wire '${wire}' has arity ${target.sig.args.length}`,
    )
  }
  const step: ProofStep = { rule: 'bodyAttach', wireId: wire, content: comp, params: [] }
  try {
    applyStep(diagram, step, ctx, orientation)
  } catch (error) {
    throw new Error(
      `named relation instantiation '${name}' is not applicable at '${wire}': ${error instanceof Error ? error.message : String(error)}`,
    )
  }
  return step
}
