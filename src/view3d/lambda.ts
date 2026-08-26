import type { NodeId, RegionId } from '../kernel/diagram/diagram'
import type { PathSeg } from '../kernel/term/reduce'
import type { Term } from '../kernel/term/term'
import { termGeometry, type NodeGeometry } from '../view/bend'
import type {
  LambdaPhase,
  LambdaStrokeFrame,
  LambdaStrokeLineage,
  LambdaStrokeRole,
} from '../view/lambda-motion'
import { lambdaFrameGeometry } from '../view/morph'
import type { Vec2 } from '../view/vec'
import {
  add3, anyPerp, cross3, norm3, scale3, type Vec3,
} from './vec3'

/** Local anatomy scale in 3D world units. The source geometry remains the
    authoritative unscaled termGeometry/LambdaStrokeFrame coordinate system. */
export const LAMBDA_SCALE = 0.12
export const LAMBDA_ARC_SEGMENTS = 32

export type LambdaPlane = {
  readonly right: Vec3
  readonly up: Vec3
  readonly normal: Vec3
}

export type LambdaEntity = {
  readonly kind: 'lambda'
  readonly key: string
  readonly node: NodeId
  /** Incident branch whose animated geometry owns this figure's pose. */
  readonly region: RegionId
  readonly term: Term
  readonly interfaceArity: number
  readonly center: Vec3
  readonly plane: LambdaPlane
  readonly scale: number
  readonly subtermPath: readonly PathSeg[]
  readonly strokeId: string
  readonly sourceStrokeId: string
  readonly role: LambdaStrokeRole
  readonly phase: LambdaPhase | null
  /** Structural provenance is populated for beta-motion frames. */
  readonly lineage: LambdaStrokeLineage | null
  readonly copyIndex: number | null
  readonly junctions: readonly [string, string] | null
  readonly destinationJunctions: readonly [string | null, string | null] | null
  /** Null means the renderer's authoritative term-wire base color. */
  readonly color: string | null
  readonly alpha?: number
  readonly pts: Vec3[]
}

export type LambdaDiagram = {
  readonly strokes: LambdaEntity[]
  readonly anchors: Map<string, Vec3>
  readonly plane: LambdaPlane
  readonly radius: number
}

export type LambdaDiagramInput = {
  readonly node: NodeId
  readonly region: RegionId
  readonly term: Term
  readonly interfaceArity: number
  readonly center: Vec3
  readonly tangent: Vec3
  readonly scale?: number
  readonly frame?: LambdaStrokeFrame
}

/** A deterministic branch-local basis. Its normal is the normalized incident
    branch direction; both drawn axes are perpendicular to that branch. */
export function lambdaPlane(branchTangent: Vec3): LambdaPlane {
  const normal = norm3(branchTangent)
  const right = anyPerp(normal)
  return { right, up: norm3(cross3(normal, right)), normal }
}

export function embedLambdaPoint(point: Vec2, center: Vec3, plane: LambdaPlane, scale: number): Vec3 {
  return add3(center, add3(scale3(plane.right, point.x * scale), scale3(plane.up, point.y * scale)))
}

function arcPoints(r: number, a0: number, a1: number): Vec2[] {
  const count = Math.max(1, Math.ceil(LAMBDA_ARC_SEGMENTS * Math.abs(a1 - a0) / (2 * Math.PI)))
  return Array.from({ length: count + 1 }, (_, index) => {
    const angle = a0 + (a1 - a0) * index / count
    return { x: r * Math.cos(angle), y: r * Math.sin(angle) }
  })
}

type StaticStroke = {
  readonly strokeId: string
  readonly sourceStrokeId: string
  readonly role: LambdaStrokeRole
  readonly phase: LambdaPhase | null
  readonly subtermPath: readonly PathSeg[]
  readonly lineage: LambdaStrokeLineage | null
  readonly copyIndex: number | null
  readonly junctions: readonly [string, string] | null
  readonly destinationJunctions: readonly [string | null, string | null] | null
  readonly color: string | null
  readonly alpha?: number
  readonly points: readonly Vec2[]
}

function deepestOwner(
  geometry: NodeGeometry,
  kind: 'arc' | 'radial' | 'exit',
  index: number,
): readonly PathSeg[] {
  const owners = geometry.occurrences.filter((occurrence) => (
    kind === 'arc'
      ? occurrence.arcIndices.includes(index)
      : kind === 'radial'
        ? occurrence.radialIndices.includes(index)
        : occurrence.includeExit
  ))
  owners.sort((left, right) => right.path.length - left.path.length)
  return owners[0]?.path ?? []
}

function staticStrokes(geometry: NodeGeometry): StaticStroke[] {
  const out: StaticStroke[] = []
  geometry.arcs.forEach((arc, index) => out.push({
    strokeId: `arc:${index}`,
    sourceStrokeId: `arc:${index}`,
    role: arc.kind === 'lam' ? 'lambda' : arc.kind === 'app' ? 'application' : 'free-rail',
    phase: null,
    subtermPath: deepestOwner(geometry, 'arc', index),
    lineage: null,
    copyIndex: null,
    junctions: null,
    destinationJunctions: null,
    color: null,
    points: arcPoints(arc.r, arc.a0, arc.a1),
  }))
  geometry.radials.forEach((radial, index) => {
    const from = { x: Math.cos(radial.angle) * radial.r0, y: Math.sin(radial.angle) * radial.r0 }
    const to = { x: Math.cos(radial.angle) * radial.r1, y: Math.sin(radial.angle) * radial.r1 }
    out.push({
      strokeId: `radial:${index}`,
      sourceStrokeId: `radial:${index}`,
      role: radial.kind === 'var' ? 'variable' : radial.kind === 'port' ? 'free-port' : 'fn-connector',
      phase: null,
      subtermPath: deepestOwner(geometry, 'radial', index),
      lineage: null,
      copyIndex: null,
      junctions: null,
      destinationJunctions: null,
      color: null,
      points: [from, to],
    })
  })
  if (geometry.exitArc !== null) out.push({
    strokeId: 'exit:arc', sourceStrokeId: 'exit:arc', role: 'output-arc',
    phase: null, subtermPath: deepestOwner(geometry, 'exit', 0),
    lineage: null, copyIndex: null, junctions: null, color: null,
    destinationJunctions: null,
    points: arcPoints(geometry.exitArc.r, geometry.exitArc.a0, geometry.exitArc.a1),
  })
  if (geometry.exitLine !== null) out.push({
    strokeId: 'exit:line', sourceStrokeId: 'exit:line', role: 'output-line',
    phase: null, subtermPath: deepestOwner(geometry, 'exit', 0),
    lineage: null, copyIndex: null, junctions: null, color: null,
    destinationJunctions: null,
    points: geometry.exitLine,
  })
  return out
}

function pathFromOwner(ownerId: string | null): readonly PathSeg[] {
  if (ownerId === null || ownerId === 'root') return []
  if (!ownerId.startsWith('root/')) return []
  const path = ownerId.slice('root/'.length).split('/')
  return path.every((segment) => segment === 'body' || segment === 'fn' || segment === 'argument')
    ? path as PathSeg[]
    : []
}

function frameStrokes(frame: LambdaStrokeFrame): StaticStroke[] {
  const strokes: StaticStroke[] = frame.strokes.map((stroke) => ({
    strokeId: stroke.id,
    sourceStrokeId: stroke.originId,
    role: stroke.role,
    phase: frame.phase,
    subtermPath: pathFromOwner(stroke.ownerId),
    lineage: stroke.lineage,
    copyIndex: stroke.copyIndex,
    junctions: [stroke.points[0].junction, stroke.points[1].junction],
    destinationJunctions: [stroke.points[0].destinationJunction, stroke.points[1].destinationJunction],
    color: stroke.color,
    points: stroke.geometry.kind === 'arc'
      ? arcPoints(stroke.geometry.r, stroke.geometry.a0, stroke.geometry.a1)
      : [stroke.geometry.from, stroke.geometry.to],
  }))
  for (const socket of frame.sockets) {
    if (socket.amount <= 0.002) continue
    const radius = 0.16 + socket.copyIndex * 0.025
    strokes.push({
      strokeId: `socket:${socket.copyIndex}`,
      sourceStrokeId: socket.sourceOccurrenceId,
      role: 'argument-connector',
      phase: frame.phase,
      subtermPath: pathFromOwner(socket.sourceOccurrenceId),
      lineage: 'argument',
      copyIndex: socket.copyIndex,
      junctions: [socket.sourceOccurrenceId, socket.sourceOccurrenceId],
      destinationJunctions: null,
      color: '#f0bd55',
      alpha: socket.amount,
      points: arcPoints(radius, 0, 2 * Math.PI).map((point) => ({
        x: point.x + socket.point.x,
        y: point.y + socket.point.y,
      })),
    })
  }
  return strokes
}

/** Embed either the authoritative static termGeometry or a sampled structural
    motion frame in the term node's branch-normal local plane. */
export function lambdaDiagram(input: LambdaDiagramInput): LambdaDiagram {
  const scale = input.scale ?? LAMBDA_SCALE
  const plane = lambdaPlane(input.tangent)
  const geometry = input.frame === undefined
    ? termGeometry(input.term, input.interfaceArity)
    : lambdaFrameGeometry(input.frame)
  const source = input.frame === undefined ? staticStrokes(geometry) : frameStrokes(input.frame)
  const strokes = source.map((stroke): LambdaEntity => ({
    kind: 'lambda',
    key: `t:${input.node}:${encodeURIComponent(stroke.strokeId)}`,
    node: input.node,
    region: input.region,
    term: input.term,
    interfaceArity: input.interfaceArity,
    center: input.center,
    plane,
    scale,
    subtermPath: stroke.subtermPath,
    strokeId: stroke.strokeId,
    sourceStrokeId: stroke.sourceStrokeId,
    role: stroke.role,
    phase: stroke.phase,
    lineage: stroke.lineage,
    copyIndex: stroke.copyIndex,
    junctions: stroke.junctions,
    destinationJunctions: stroke.destinationJunctions,
    color: stroke.color,
    ...(stroke.alpha === undefined ? {} : { alpha: stroke.alpha }),
    pts: stroke.points.map((point) => embedLambdaPoint(point, input.center, plane, scale)),
  }))
  return {
    strokes,
    anchors: new Map(Object.entries(geometry.portAnchors).map(([key, point]) => [
      key,
      embedLambdaPoint(point, input.center, plane, scale),
    ])),
    plane,
    radius: geometry.outerRadius * scale,
  }
}

export function lambdaOutlineRadius(term: Term, interfaceArity: number, scale = LAMBDA_SCALE): number {
  return termGeometry(term, interfaceArity).outerRadius * scale
}
