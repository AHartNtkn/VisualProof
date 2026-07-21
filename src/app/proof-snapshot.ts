import { diagramToJson } from '../kernel/diagram/json'
import { stepToJson } from '../kernel/proof/json'
import type { TrackDirection, ProofTimeline } from './session'
import { timelineActiveActions, timelineCurrent } from './session'
import type { ProofAllocation } from '../kernel/proof/action'

export type ProofSnapshot = {
  readonly diagram: unknown
  readonly actions: readonly {
    readonly label: string
    readonly steps: readonly unknown[]
    readonly placements: readonly {
      readonly introducedNode: number
      readonly x: number
      readonly y: number
    }[]
    readonly allocation?: ProofAllocation
  }[]
  readonly cursor: number
  readonly orientation: TrackDirection
  readonly fixedSide?: TrackDirection
}

/** Authoritative, JSON-compatible proof state used by exact preservation evidence. */
export function proofSnapshot(
  timeline: ProofTimeline,
  orientation: TrackDirection,
  fixedSide?: TrackDirection,
): ProofSnapshot {
  const snapshot: ProofSnapshot = {
    diagram: diagramToJson(timelineCurrent(timeline)),
    actions: timelineActiveActions(timeline).map((action) => ({
      label: action.label,
      steps: action.steps.map(stepToJson),
      placements: action.placements.map((placement) => ({ ...placement })),
      ...(action.allocation === undefined ? {} : { allocation: {
        regions: [...action.allocation.regions],
        nodes: [...action.allocation.nodes],
        wires: [...action.allocation.wires],
      } }),
    })),
    cursor: timeline.cursor,
    orientation,
    ...(fixedSide === undefined ? {} : { fixedSide }),
  }
  return snapshot
}
