import type { Engine } from './engine'
import type { DragProjection } from './constraints'
import { commitBodyPositions, projectDragToSemanticFrontier } from './constraints'
import { settleStep } from './relax'
import type { Vec2 } from './vec'

/** Cursor-relative carrier offsets captured at the start of a physics drag. */
export type PhysicsDrag = {
  readonly bodies: ReadonlyMap<string, Vec2>
  /** Legal positions at pointer-down, used to make cancellation transactional. */
  readonly origins: ReadonlyMap<string, Vec2>
}

/** The current sample of an active physics drag, in engine coordinates. */
export type ActivePhysicsDrag = {
  readonly drag: PhysicsDrag
  readonly cursor: Vec2
}

/**
 * Project and commit one cursor sample through the complete semantic geometry
 * contract. Pointermove and pointerup use this same boundary, so the final
 * position cannot depend on animation-frame timing. Animation frames only
 * advance the solver through `advanceInteractivePhysics`.
 */
export function commitPhysicsDragSample(e: Engine, active: ActivePhysicsDrag): DragProjection {
  const targets = new Map<string, Vec2>()
  for (const [id, offset] of active.drag.bodies) {
    targets.set(id, { x: active.cursor.x + offset.x, y: active.cursor.y + offset.y })
  }
  const projection = projectDragToSemanticFrontier(e, targets)
  commitBodyPositions(e, projection.positions)
  return projection
}

/** Restore the grabbed carriers to their legal pointer-down positions. */
export function cancelPhysicsDrag(e: Engine, drag: PhysicsDrag): void {
  commitBodyPositions(e, drag.origins)
}

/**
 * Advance one interactive physics frame. An active drag always advances the
 * solver, even when passive relaxation is paused for a stable connection
 * gesture. Grabbed carriers and persistent pins are the only excluded DOFs;
 * every other body, rotation, junction, and wire carrier remains live.
 */
export function advanceInteractivePhysics(
  e: Engine,
  persistentPins: ReadonlySet<string>,
  active: ActivePhysicsDrag | null,
  allowPassiveRelaxation: boolean,
): void {
  if (active === null && !allowPassiveRelaxation) return

  const pinned = new Set(persistentPins)
  if (active !== null) for (const id of active.drag.bodies.keys()) pinned.add(id)
  settleStep(e, pinned.size === 0 ? null : pinned)
}
