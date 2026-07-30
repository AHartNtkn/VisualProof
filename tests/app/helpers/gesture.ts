import type { Endpoint, RegionId, WireId } from '../../../src/kernel/diagram/diagram'
import type { PointerSample } from '../../../src/app/interact/viewport'
import { pkey, type Engine } from '../../../src/view/engine'
import { computeLegs } from '../../../src/view/wires'
import type { Vec2 } from '../../../src/view/vec'

export function pointerSample(point: Vec2, button = 0): PointerSample {
  return {
    pointerId: 1,
    button,
    client: point,
    screen: point,
    world: point,
    hit: null,
    shiftKey: false,
    ctrlKey: false,
    altKey: false,
    metaKey: false,
  }
}

/**
 * The freshly built engine stacks every body near the origin; spread the
 * fixture out so each probe point touches exactly the intended object.
 */
export function place(engine: Engine, bodyId: string, pos: Vec2): Vec2 {
  const body = engine.bodies.get(bodyId)
  if (body === undefined) throw new Error(`no body '${bodyId}'`)
  body.pos = pos
  return pos
}

export function placeRegion(
  engine: Engine,
  region: RegionId,
  center: Vec2,
  radius: number,
): Vec2 {
  engine.regions.set(region, { center, radius, support: [] })
  return center
}

/** World position of a wire's terminal at one endpoint. */
export function endpointPoint(
  engine: Engine,
  wire: WireId,
  endpoint: Endpoint,
): Vec2 {
  const key = pkey(endpoint.port)
  for (const geometry of computeLegs(engine)) {
    if (geometry.leg.wid !== wire || geometry.pts.length === 0) continue
    if (geometry.leg.from.body === endpoint.node && geometry.leg.from.key === key) {
      return geometry.pts[0]!
    }
    if (geometry.leg.to.body === endpoint.node && geometry.leg.to.key === key) {
      return geometry.pts.at(-1)!
    }
  }
  throw new Error(`no leg terminal for ${wire} at ${endpoint.node}`)
}

export function farBlank(): Vec2 {
  return { x: 4000, y: 4000 }
}
