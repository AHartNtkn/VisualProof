import type { Diagram } from '../kernel/diagram/diagram'
import type { ProofAction } from '../kernel/proof/action'
import { applyAction, introducedNodeIds } from '../kernel/proof/action'
import type { ProofContext } from '../kernel/proof/step'
import type { Engine } from '../view/engine'
import { seedBodyPlacement } from '../view/placement'
import type { Vec2 } from '../view/vec'

/** Reconstruct presentation from the proof itself. A placement belongs to one
    body epoch, which ends the first time its id disappears at a constituent
    step boundary. Action-wide indices are resolved only after that action's
    complete replay, using the same kernel ordering that validates the record. */
export function seedActionHistoryPlacements(
  engine: Engine,
  initial: Diagram,
  activeActions: readonly ProofAction[],
  ctx: ProofContext,
  orientation: 'forward' | 'backward',
): void {
  const placements = new Map<string, Vec2>()
  let current = initial
  for (const action of activeActions) {
    const actionInput = current
    let previousStep = current
    current = applyAction(current, action, ctx, orientation, (nextStep) => {
      for (const node of placements.keys()) {
        if (previousStep.nodes[node] !== undefined && nextStep.nodes[node] === undefined) {
          placements.delete(node)
        }
      }
      previousStep = nextStep
    })
    const introduced = introducedNodeIds(actionInput, current)
    for (const placement of action.placements) {
      const node = introduced[placement.introducedNode]
      if (node !== undefined) placements.set(node, { x: placement.x, y: placement.y })
    }
  }
  for (const [node, at] of placements) seedBodyPlacement(engine, node, at)
}
