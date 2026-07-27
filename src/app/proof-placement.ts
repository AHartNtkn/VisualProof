import type { Diagram } from '../kernel/diagram/diagram'
import type { ProofAction } from '../kernel/proof/action'
import { applyAction, introducedNodeIds } from '../kernel/proof/action'
import type { ProofContext } from '../kernel/proof/context'
import { assertProofContext } from '../kernel/proof/context'
import type { Engine } from '../view/engine'
import { seedBodyPlacement } from '../view/placement'
import type { Vec2 } from '../view/vec'
import type { Replay } from './replay'

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
  assertProofContext(ctx)
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

/**
 * Reconstruct placement hints from the proof half that owns the displayed
 * replay state. Backward display order is synthetic; its placement history is
 * always replayed from the exact rhs in the original backward action order.
 */
export function seedReplayPlacements(
  engine: Engine,
  replay: Replay,
  cursor: number,
  ctx: ProofContext,
): void {
  if (!Number.isInteger(cursor) || cursor < 0 || cursor > replay.actionCount) {
    throw new Error(`replay placement cursor ${cursor} is out of range [0, ${replay.actionCount}]`)
  }
  if (cursor <= replay.meetingIndex) {
    const transitions = replay.transitions.slice(0, cursor)
    if (transitions.some(({ half }) => half !== 'forward')) {
      throw new Error('replay forward placement prefix contains a backward transition')
    }
    seedActionHistoryPlacements(
      engine,
      replay.diagramAt(0),
      transitions.map(({ action }) => action),
      ctx,
      'forward',
    )
    return
  }

  const transitions = replay.transitions.slice(cursor).reverse()
  if (transitions.some(({ half }) => half !== 'backward')) {
    throw new Error('replay backward placement prefix contains a forward transition')
  }
  seedActionHistoryPlacements(
    engine,
    replay.diagramAt(replay.actionCount),
    transitions.map(({ action }) => action),
    ctx,
    'backward',
  )
}
