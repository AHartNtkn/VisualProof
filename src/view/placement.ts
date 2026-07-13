import type { Diagram } from '../kernel/diagram/diagram'
import type { PlacementHint } from '../kernel/proof/action'
import { introducedNodeIds } from '../kernel/proof/action'
import type { Engine } from './engine'
import type { Vec2 } from './vec'

export type BodyPlacement = {
  readonly id: string
  readonly origin: Vec2
}

/** Begin a semantic placement preview without changing diagram membership or
    recomputing its region circle. The fixed region geometry remains honest
    while the user chooses a destination. */
export function beginBodyPlacement(engine: Engine, id: string): BodyPlacement {
  const body = engine.bodies.get(id)
  if (body === undefined) throw new Error(`cannot place unknown body '${id}'`)
  return { id, origin: { ...body.pos } }
}

/** Move only the view body. The caller transiently pins this body in the shared
    solver so every other body and wire degree of freedom can keep settling. */
export function previewBodyPlacement(engine: Engine, placement: BodyPlacement, at: Vec2): void {
  const body = engine.bodies.get(placement.id)
  if (body !== undefined) body.pos = { ...at }
}

/** Cancel a preview exactly, leaving diagram state untouched. */
export function cancelBodyPlacement(engine: Engine, placement: BodyPlacement): void {
  const body = engine.bodies.get(placement.id)
  if (body !== undefined) body.pos = { ...placement.origin }
}

/** Seed a newly-created body at the invocation point before relaxation. */
export function seedBodyPlacement(engine: Engine, id: string, at: Vec2): void {
  const body = engine.bodies.get(id)
  if (body !== undefined) body.pos = { ...at }
}

/** Apply persisted presentation hints after the complete action's diagram has
    been reconciled into the engine. The kernel validates every index first. */
export function seedActionPlacements(
  engine: Engine,
  before: Diagram,
  after: Diagram,
  placements: readonly PlacementHint[],
): void {
  const introduced = introducedNodeIds(before, after)
  for (const placement of placements) {
    const node = introduced[placement.introducedNode]
    if (node !== undefined) seedBodyPlacement(engine, node, { x: placement.x, y: placement.y })
  }
}
