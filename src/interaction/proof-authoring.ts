import { DiagramBuilder } from '../kernel/diagram/builder'
import { mkDiagramWithBoundary, type DiagramWithBoundary } from '../kernel/diagram/boundary'
import type { Diagram, RegionId, WireId } from '../kernel/diagram/diagram'
import type { SubgraphSelection } from '../kernel/diagram/subgraph/selection'
import type { ProofContext } from '../kernel/proof/context'
import { assertProofContext } from '../kernel/proof/context'
import type { ProofStep } from '../kernel/proof/step'
import { findDeiterationEvidence } from '../kernel/rules/iteration'
import { findInconsistentCutEvidence } from '../kernel/rules/inconsistent-cut'
import { RuleError } from '../kernel/rules/error'
import type { ActionDescriptor } from './actions'
import { orphanedWires } from './edit'

export function erasureStep(diagram: Diagram, selection: SubgraphSelection): ProofStep {
  const existing = new Set(selection.wires)
  const riders = orphanedWires(diagram, new Set(selection.nodes))
    .filter((wire) => !existing.has(wire) && diagram.wires[wire]!.scope === selection.region)
  return {
    rule: 'erasure',
    sel: riders.length === 0
      ? selection
      : { ...selection, wires: [...selection.wires, ...riders] },
  }
}

export function deiterationStep(
  diagram: Diagram,
  selection: SubgraphSelection,
  fuel: number,
): ProofStep {
  return {
    rule: 'deiteration',
    sel: selection,
    ...findDeiterationEvidence(diagram, selection, fuel),
  }
}

export function inconsistentCutStep(diagram: Diagram, region: RegionId, fuel: number): ProofStep | null {
  const result = findInconsistentCutEvidence(diagram, region, fuel)
  if (result.status === 'undecided') {
    throw new RuleError('inconsistency is undecided under the current fuel')
  }
  return result.status === 'certified' ? {
    rule: 'inconsistentCutElim', region,
    first: result.first, second: result.second, certificate: result.certificate,
  } : null
}

export function contextualDeletionStep(
  diagram: Diagram,
  selection: SubgraphSelection,
  actions: readonly ActionDescriptor[],
  fuel: number,
): ProofStep | null {
  const has = (kind: ActionDescriptor['kind']): boolean => actions.some((action) => action.kind === kind)
  if (has('doubleCutElim')) return { rule: 'doubleCutElim', region: selection.regions[0]! }
  if (has('vacuousElim')) return { rule: 'vacuousElim', region: selection.regions[0]! }
  if (has('inconsistentCutElim')) {
    const step = inconsistentCutStep(diagram, selection.regions[0]!, fuel)
    if (step !== null) return step
  }
  if (has('erase')) return erasureStep(diagram, selection)
  return has('deiterate') ? deiterationStep(diagram, selection, fuel) : null
}

export function foldedComprehension(context: ProofContext, name: string): DiagramWithBoundary {
  assertProofContext(context)
  const relation = context.relations.get(name)
  if (relation === undefined) throw new Error(`unknown relation '${name}'`)
  const builder = new DiagramBuilder()
  const ref = builder.ref(builder.root, name, relation.boundary.length)
  const boundary: WireId[] = []
  for (let index = 0; index < relation.boundary.length; index++) {
    boundary.push(builder.wire(builder.root, [{ node: ref, port: { kind: 'arg', index } }]))
  }
  return mkDiagramWithBoundary(builder.build(), boundary)
}
