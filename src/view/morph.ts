import type { NodeArc, NodeGeometry, NodeRadial } from './bend'
import type { LambdaStrokeFrame } from './lambda-motion'
import type { Vec2 } from './vec'

const lerp = (from: number, to: number, progress: number): number =>
  from + (to - from) * progress

const lerpPoint = (from: Vec2, to: Vec2, progress: number): Vec2 => ({
  x: lerp(from.x, to.x, progress),
  y: lerp(from.y, to.y, progress),
})

const collapsedArc = (arc: NodeArc): NodeArc => {
  const middle = (arc.a0 + arc.a1) / 2
  return { ...arc, a0: middle, a1: middle }
}

const interpolateArc = (from: NodeArc, to: NodeArc, progress: number): NodeArc => ({
  ...(progress < 0.5 ? from : to),
  r: lerp(from.r, to.r, progress),
  a0: lerp(from.a0, to.a0, progress),
  a1: lerp(from.a1, to.a1, progress),
})

const collapsedRadial = (radial: NodeRadial): NodeRadial => {
  const middle = (radial.r0 + radial.r1) / 2
  return { ...radial, r0: middle, r1: middle }
}

const interpolateRadial = (from: NodeRadial, to: NodeRadial, progress: number): NodeRadial => ({
  ...(progress < 0.5 ? from : to),
  angle: lerp(from.angle, to.angle, progress),
  r0: lerp(from.r0, to.r0, progress),
  r1: lerp(from.r1, to.r1, progress),
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
  const radialCount = Math.max(from.radials.length, to.radials.length)
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

    const radials: NodeRadial[] = []
    for (let index = 0; index < radialCount; index++) {
      const fromRadial = from.radials[index]
      const toRadial = to.radials[index]
      if (fromRadial !== undefined && toRadial !== undefined) {
        radials.push(interpolateRadial(fromRadial, toRadial, progress))
      } else if (fromRadial !== undefined) {
        radials.push(interpolateRadial(fromRadial, collapsedRadial(fromRadial), progress))
      } else if (toRadial !== undefined) {
        radials.push(interpolateRadial(collapsedRadial(toRadial), toRadial, progress))
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

    const exitArc = from.exitArc === null && to.exitArc === null
      ? null
      : (() => {
          const fromArc = from.exitArc ?? {
            r: to.exitArc!.r,
            a0: (to.exitArc!.a0 + to.exitArc!.a1) / 2,
            a1: (to.exitArc!.a0 + to.exitArc!.a1) / 2,
          }
          const toArc = to.exitArc ?? {
            r: from.exitArc!.r,
            a0: (from.exitArc!.a0 + from.exitArc!.a1) / 2,
            a1: (from.exitArc!.a0 + from.exitArc!.a1) / 2,
          }
          return {
            r: lerp(fromArc.r, toArc.r, progress),
            a0: lerp(fromArc.a0, toArc.a0, progress),
            a1: lerp(fromArc.a1, toArc.a1, progress),
          }
        })()
    const exitLine = from.exitLine === null && to.exitLine === null
      ? null
      : (() => {
          const fromLine = from.exitLine ?? [to.exitLine![0], to.exitLine![0]] as const
          const toLine = to.exitLine ?? [from.exitLine![0], from.exitLine![0]] as const
          return [
            lerpPoint(fromLine[0], toLine[0], progress),
            lerpPoint(fromLine[1], toLine[1], progress),
          ] as const
        })()

    return {
      outerRadius: lerp(from.outerRadius, to.outerRadius, progress),
      arcs,
      radials,
      headAnchor,
      portAnchors,
      exitArc,
      exitLine,
      occurrences: [],
    }
  }
}

/**
 * Project a sampled structural beta frame back into the established circular
 * node-geometry contract. Motion colors remain on the frame; this projection
 * supplies geometry, anchors, bounds, and the ordinary painter's stroke kinds.
 */
export function lambdaFrameGeometry(frame: LambdaStrokeFrame): NodeGeometry {
  const arcs: NodeArc[] = []
  const radials: NodeRadial[] = []
  const portAnchors: Record<string, Vec2> = {}
  let exitArc: NodeGeometry['exitArc'] = null
  let exitLine: NodeGeometry['exitLine'] = null
  let outerRadius = 0

  for (const stroke of frame.strokes) {
    for (const point of stroke.points) outerRadius = Math.max(outerRadius, Math.hypot(point.x, point.y))
    if (stroke.role === 'free-port') {
      const slot = /^interface:free:(\d+):/.exec(stroke.id)?.[1]
      if (slot !== undefined) portAnchors[`f:${slot}`] = { ...stroke.points[1] }
    }
    if (stroke.role === 'output-line') {
      portAnchors.out = { ...stroke.points[1] }
      if (stroke.geometry.kind !== 'segment') throw new Error('Lambda output line is not a segment')
      exitLine = [stroke.geometry.from, stroke.geometry.to]
      continue
    }
    if (stroke.role === 'output-arc') {
      if (stroke.geometry.kind !== 'arc') throw new Error('Lambda output arc is not an arc')
      exitArc = {
        r: stroke.geometry.r,
        a0: stroke.geometry.a0,
        a1: stroke.geometry.a1,
      }
      continue
    }
    if (stroke.geometry.kind === 'arc') {
      arcs.push({
        r: stroke.geometry.r,
        a0: stroke.geometry.a0,
        a1: stroke.geometry.a1,
        kind: stroke.role === 'lambda' ? 'lam' : stroke.role === 'application' ? 'app' : 'rail',
        hueRow: stroke.geometry.r,
      })
      continue
    }
    const fromRadius = Math.hypot(stroke.geometry.from.x, stroke.geometry.from.y)
    const toRadius = Math.hypot(stroke.geometry.to.x, stroke.geometry.to.y)
    radials.push({
      angle: Math.atan2(stroke.geometry.from.y, stroke.geometry.from.x),
      r0: fromRadius,
      r1: toRadius,
      kind: stroke.role === 'variable'
        ? 'var'
        : stroke.role === 'free-drop' || stroke.role === 'free-port'
          ? 'port'
          : 'output',
      hueRow: stroke.role === 'variable' ? fromRadius : null,
    })
  }

  return {
    outerRadius: outerRadius + 0.5,
    arcs,
    radials,
    headAnchor: null,
    portAnchors,
    exitArc,
    exitLine,
    occurrences: [],
  }
}
