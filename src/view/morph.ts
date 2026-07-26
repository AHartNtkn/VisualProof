import type { NodeArc, NodeGeometry } from './bend'
import type { Vec2 } from './vec'

const lerp = (from: number, to: number, progress: number): number =>
  from + (to - from) * progress

const lerpPoint = (from: Vec2, to: Vec2, progress: number): Vec2 => ({
  x: lerp(from.x, to.x, progress),
  y: lerp(from.y, to.y, progress),
})

const collapsedArc = (arc: NodeArc): NodeArc => {
  const middle = (arc.a0 + arc.a1) / 2
  return { r: arc.r, a0: middle, a1: middle }
}

const interpolateArc = (from: NodeArc, to: NodeArc, progress: number): NodeArc => ({
  r: lerp(from.r, to.r, progress),
  a0: lerp(from.a0, to.a0, progress),
  a1: lerp(from.a1, to.a1, progress),
})

/**
 * Interpolate one whole semantic-node geometry into another.
 *
 * Geometry is the only transition state. Exact storage anchors that survive
 * interpolate by key; disappearing and appearing anchors contract to or grow
 * from the centre. No term-substructure or alternate grid representation is
 * retained alongside it.
 */
export function mkGeomMorph(
  from: NodeGeometry,
  to: NodeGeometry,
): (progress: number) => NodeGeometry {
  const arcCount = Math.max(from.arcs.length, to.arcs.length)
  const anchorKeys = [...new Set([
    ...Object.keys(from.portAnchors),
    ...Object.keys(to.portAnchors),
  ])]
  const center = { x: 0, y: 0 }

  return (progress: number): NodeGeometry => {
    if (progress <= 0) return from
    if (progress >= 1) return to

    const arcs: NodeArc[] = []
    for (let index = 0; index < arcCount; index++) {
      const fromArc = from.arcs[index]
      const toArc = to.arcs[index]
      if (fromArc !== undefined && toArc !== undefined) {
        arcs.push(interpolateArc(fromArc, toArc, progress))
      } else if (fromArc !== undefined) {
        arcs.push(interpolateArc(fromArc, collapsedArc(fromArc), progress))
      } else if (toArc !== undefined) {
        arcs.push(interpolateArc(collapsedArc(toArc), toArc, progress))
      }
    }

    const portAnchors: Record<string, Vec2> = {}
    for (const key of anchorKeys) {
      portAnchors[key] = lerpPoint(
        from.portAnchors[key] ?? center,
        to.portAnchors[key] ?? center,
        progress,
      )
    }

    const headAnchor = from.headAnchor === null && to.headAnchor === null
      ? null
      : lerpPoint(from.headAnchor ?? center, to.headAnchor ?? center, progress)

    return {
      outerRadius: lerp(from.outerRadius, to.outerRadius, progress),
      arcs,
      headAnchor,
      portAnchors,
    }
  }
}
