import { DiagramBuilder } from '../kernel/diagram/builder'
import type { Diagram, RegionId, WireId } from '../kernel/diagram/diagram'
import { mkDiagramWithBoundary, type DiagramWithBoundary } from '../kernel/diagram/boundary'
import type { ProofContext } from '../kernel/proof/context'
import { assertProofContext } from '../kernel/proof/context'
import { applyStep, type ProofStep } from '../kernel/proof/step'

export type ProofOrientation = 'forward' | 'backward'

/** Construct the closed reference comprehension for one named relation. */
export function foldedComprehension(ctx: ProofContext, name: string): DiagramWithBoundary {
  assertProofContext(ctx)
  const relation = ctx.relations.get(name)
  if (relation === undefined) throw new Error(`unknown named relation '${name}'`)
  const builder = new DiagramBuilder()
  const ref = builder.ref(builder.root, name, relation.boundary.length)
  const boundary: WireId[] = []
  for (let index = 0; index < relation.boundary.length; index++) {
    boundary.push(builder.wire(builder.root, [{ node: ref, port: { kind: 'arg', index } }]))
  }
  return mkDiagramWithBoundary(builder.build(), boundary)
}

/**
 * Resolve an explicit named-relation request into a submission-ready closed
 * comprehension step. Named definitions never infer host dependencies: every
 * definition boundary must be an argument position on the selected bubble.
 */
export function resolveNamedRelationInstantiation(
  diagram: Diagram,
  bubble: RegionId,
  ctx: ProofContext,
  name: string,
  orientation: ProofOrientation,
): ProofStep {
  assertProofContext(ctx)
  const relation = ctx.relations.get(name)
  if (relation === undefined) throw new Error(`unknown named relation '${name}'`)
  const target = diagram.regions[bubble]
  if (target === undefined) throw new Error(`named relation instantiation target '${bubble}' does not exist`)
  if (target.kind !== 'bubble') throw new Error(`named relation instantiation requires a bubble target; '${bubble}' is a ${target.kind}`)
  if (relation.boundary.length !== target.arity) {
    throw new Error(
      `named relation arity mismatch: '${name}' has ${relation.boundary.length} boundary parameters but target bubble '${bubble}' has arity ${target.arity}`,
    )
  }
  const step: ProofStep = {
    rule: 'comprehensionInstantiate',
    bubble,
    comp: foldedComprehension(ctx, name),
    attachments: [],
    binders: [],
  }
  try {
    applyStep(diagram, step, ctx, orientation)
  } catch (error) {
    throw new Error(
      `named relation instantiation '${name}' is not applicable at '${bubble}': ${error instanceof Error ? error.message : String(error)}`,
    )
  }
  return step
}
