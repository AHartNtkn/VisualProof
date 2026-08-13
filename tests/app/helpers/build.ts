import type { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import type { NodeId, RegionId, WireId } from '../../../src/kernel/diagram/diagram'
import { IOTA, type Sig } from '../../../src/kernel/diagram/sig'
import type { Engine } from '../../../src/view/engine'
import type { Vec2 } from '../../../src/view/vec'
import { place } from './gesture'

/** A bare segment and the two pins that hold its quantifier. */
export type Segment = {
  readonly wire: WireId
  readonly ends: readonly [NodeId, NodeId]
}

/**
 * The bare segment at `region`: a wire whose only incidences are two pins
 * there, so its derived scope is exactly `region`. This is the drawable
 * floating existential — the shape a wire with no other attachments takes
 * now that every end is a node.
 */
export function segment(
  builder: DiagramBuilder,
  region: RegionId,
  sig: Sig = IOTA,
): Segment {
  const wire = builder.wire([], sig)
  const a = builder.pin(wire, region)
  const b = builder.pin(wire, region)
  return { wire, ends: [a, b] }
}

/** Just the wire, for fixtures that never touch the segment's geometry. */
export function bareWire(
  builder: DiagramBuilder,
  region: RegionId,
  sig: Sig = IOTA,
): WireId {
  return segment(builder, region, sig).wire
}

/**
 * Put a segment's two pins above and below `center` so the strand between
 * them passes through it, and return that midpoint: the point a gesture
 * grabs to mean "this line", clear of either terminal's halo.
 */
export function spread(engine: Engine, seg: Segment, center: Vec2): Vec2 {
  place(engine, seg.ends[0], { x: center.x, y: center.y - 30 })
  place(engine, seg.ends[1], { x: center.x, y: center.y + 30 })
  return center
}
