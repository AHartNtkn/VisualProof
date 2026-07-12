import type { Diagram } from '../diagram/diagram'
import { ProofError } from './error'
import { applyStep } from './step'
import type { ProofContext, ProofStep } from './step'

export type PlacementHint = {
  readonly introducedNode: number
  readonly x: number
  readonly y: number
}

export type ProofAction = {
  readonly label: string
  readonly steps: readonly ProofStep[]
  readonly placements: readonly PlacementHint[]
}

export function singleStepAction(
  label: string,
  step: ProofStep,
  placements: readonly PlacementHint[] = [],
): ProofAction {
  return { label, steps: [step], placements }
}

export function applyAction(
  diagram: Diagram,
  action: ProofAction,
  ctx: ProofContext,
  orientation: 'forward' | 'backward' = 'forward',
  afterStep?: (diagram: Diagram, stepIndex: number) => void,
): Diagram {
  if (action.label.length === 0) throw new ProofError('proof action label must not be empty')
  if (action.steps.length === 0) throw new ProofError(`proof action '${action.label}' must contain at least one step`)

  let current = diagram
  for (const [stepIndex, step] of action.steps.entries()) {
    try {
      current = applyStep(current, step, ctx, orientation)
    } catch (error) {
      throw new ProofError(
        `step ${stepIndex} (${step.rule}) failed: ${error instanceof Error ? error.message : String(error)}`,
      )
    }
    afterStep?.(current, stepIndex)
  }

  const introducedNodes = Object.keys(current.nodes)
    .filter((id) => diagram.nodes[id] === undefined)
    .sort()
  const placed = new Set<number>()
  for (const placement of action.placements) {
    if (!Number.isFinite(placement.x) || !Number.isFinite(placement.y)) {
      throw new ProofError(`placement coordinates must be finite for introduced node index ${placement.introducedNode}`)
    }
    if (placed.has(placement.introducedNode)) {
      throw new ProofError(`duplicate introduced node index ${placement.introducedNode}`)
    }
    if (!Number.isInteger(placement.introducedNode)
      || placement.introducedNode < 0
      || placement.introducedNode >= introducedNodes.length) {
      throw new ProofError(`introduced node index ${placement.introducedNode} is out of range`)
    }
    placed.add(placement.introducedNode)
  }

  return current
}

export function replayActions(
  diagram: Diagram,
  actions: readonly ProofAction[],
  ctx: ProofContext,
  afterStep?: (diagram: Diagram, actionIndex: number, stepIndex: number) => void,
  orientation: 'forward' | 'backward' = 'forward',
): Diagram {
  let current = diagram
  for (const [actionIndex, action] of actions.entries()) {
    try {
      current = applyAction(
        current,
        action,
        ctx,
        orientation,
        (next, stepIndex) => afterStep?.(next, actionIndex, stepIndex),
      )
    } catch (error) {
      throw new ProofError(
        `action ${actionIndex} ('${action.label}') failed: ${error instanceof Error ? error.message : String(error)}`,
      )
    }
  }
  return current
}
