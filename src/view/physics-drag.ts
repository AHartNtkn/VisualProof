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

/** Exact configuration snapshot (body poses + wire manifold points): the rest
    certificate's validity check. Cheap (a few hundred floats). */
function stateSnap(e: Engine): number[] {
  const out: number[] = []
  for (const b of e.bodies.values()) out.push(b.pos.x, b.pos.y, b.theta)
  for (const w of e.wires.values()) {
    for (const p of w.net.junctions) out.push(p.x, p.y)
    for (const [u, v] of w.net.edges) out.push(u, v)
  }
  return out
}
const sameSnap = (a: readonly number[], b: readonly number[]): boolean =>
  a.length === b.length && a.every((v, i) => v === b[i])

/** Proven-rest certificates per engine: a frame in which the step operator
    accepted nothing is a bit-stable fixed point FOR THAT state and pin set
    (deterministic + memoryless), so physics is skipped until either changes.
    Exact-snapshot comparison makes this self-healing: any mutation from any
    path (rewrites, gestures, direct edits) changes the snapshot and physics
    resumes — no invalidation hooks to forget. */
const restCert = new WeakMap<Engine, { pinsKey: string; snap: number[] }>()

/**
 * Advance one interactive physics frame. An active drag always advances the
 * solver, even when passive relaxation is paused for a stable connection
 * gesture. Grabbed carriers and persistent pins are the only excluded DOFs;
 * every other body, rotation, and wire coordinate remains live. A proven rest
 * (see `restCert`) costs nothing per frame until the state or pins change.
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
  const pinsKey = [...pinned].sort().join('|')
  const cert = restCert.get(e)
  if (cert !== undefined && cert.pinsKey === pinsKey && sameSnap(cert.snap, stateSnap(e))) return
  const moved = settleStep(e, pinned.size === 0 ? null : pinned)
  if (moved) restCert.delete(e)
  else restCert.set(e, { pinsKey, snap: stateSnap(e) })
}
