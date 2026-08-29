import type { Diagram } from '../diagram/diagram'
import { derivedScope } from '../diagram/regions'
import {
  orphanedWires,
  type SubgraphSelection,
} from '../diagram/subgraph/selection'
import { findDeiterationEvidence } from '../rules/iteration'
import type { ProofStep } from './step'

function erasureSelection(
  diagram: Diagram,
  selection: SubgraphSelection,
): SubgraphSelection {
  const existing = new Set(selection.wires)
  const riders = orphanedWires(diagram, new Set(selection.nodes))
    .filter((wire) =>
      !existing.has(wire) && derivedScope(diagram, wire) === selection.region)
  return riders.length === 0
    ? selection
    : { ...selection, wires: [...selection.wires, ...riders] }
}

export function erasureStep(
  diagram: Diagram,
  selection: SubgraphSelection,
): ProofStep {
  return { rule: 'erasure', sel: erasureSelection(diagram, selection) }
}

export function deiterationStep(
  diagram: Diagram,
  selection: SubgraphSelection,
): ProofStep {
  return {
    rule: 'deiteration',
    sel: selection,
    ...findDeiterationEvidence(diagram, selection),
  }
}
