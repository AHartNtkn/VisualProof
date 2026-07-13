import type { Diagram } from '../diagram/diagram'
import type { NodeId, RegionId, WireId } from '../diagram/diagram'
import type { IdReservation } from '../diagram/subgraph/freshId'
import { ProofError } from './error'
import { applyStep } from './step'
import type { ProofContext, ProofStep } from './step'

export type PlacementHint = {
  readonly introducedNode: number
  readonly x: number
  readonly y: number
}

/** Non-logical exclusions consulted only when a proof step allocates fresh IDs. */
export type ProofAllocation = {
  readonly regions: readonly RegionId[]
  readonly nodes: readonly NodeId[]
  readonly wires: readonly WireId[]
}

export type ProofAction = {
  readonly label: string
  readonly steps: readonly ProofStep[]
  readonly placements: readonly PlacementHint[]
  readonly allocation?: ProofAllocation
}

function checkedIds(ids: unknown, field: string, namespace: string): ReadonlySet<string> {
  if (!Array.isArray(ids)) throw new ProofError(`proof action allocation ${field} must be an array`)
  const seen = new Set<string>()
  for (const id of ids) {
    if (typeof id !== 'string' || id.length === 0) {
      throw new ProofError(`proof action allocation ${namespace} ids must be non-empty strings`)
    }
    if (seen.has(id)) throw new ProofError(`duplicate ${namespace} allocation id '${id}'`)
    seen.add(id)
  }
  return seen
}

export function allocationReservation(allocation?: ProofAllocation): IdReservation {
  if (allocation === undefined) return { regions: new Set(), nodes: new Set(), wires: new Set() }
  if (allocation === null || typeof allocation !== 'object') {
    throw new ProofError('proof action allocation must be an object')
  }
  return {
    regions: checkedIds(allocation.regions, 'regions', 'region'),
    nodes: checkedIds(allocation.nodes, 'nodes', 'node'),
    wires: checkedIds(allocation.wires, 'wires', 'wire'),
  }
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
  const reservation = allocationReservation(action.allocation)

  let current = diagram
  for (const [stepIndex, step] of action.steps.entries()) {
    try {
      current = applyStep(current, step, ctx, orientation, reservation)
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
