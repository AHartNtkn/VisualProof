import type { Diagram, NodeId, RegionId, WireId, Port } from '../kernel/diagram/diagram'
import { portKey } from '../kernel/diagram/diagram'
import { polarity } from '../kernel/diagram/regions'
import type { Vec2 } from './vec'
import { add, scale, sub, length, vec } from './vec'
import type { NodeGeometry } from './bend'
import { bendGrid, atomGeometry } from './bend'
import { trompGrid } from './tromp'

export type SceneRegion = {
  readonly id: RegionId
  readonly kind: 'sheet' | 'cut' | 'bubble'
  readonly center: Vec2
  readonly radius: number
  readonly shaded: boolean
}

export type SceneNode = {
  readonly id: NodeId
  readonly center: Vec2
  readonly geometry: NodeGeometry
}

export type SceneWire = {
  readonly id: WireId
  readonly hub: Vec2
  readonly spokes: readonly Vec2[]
}

export type Scene = {
  readonly regions: readonly SceneRegion[]
  readonly nodes: readonly SceneNode[]
  readonly wires: readonly SceneWire[]
}

/** Visual breathing room around region contents; containment holds at 0. */
const REGION_PADDING = 3

/** The world-space wire anchor of (node, port) given the node's center. */
export function anchorOf(geometry: NodeGeometry, center: Vec2, port: Port): Vec2 {
  if (port.kind === 'output') return add(center, geometry.outputAnchor)
  const key = port.kind === 'freeVar' ? port.name : `a${port.index}`
  const local = geometry.portAnchors[key]
  if (local === undefined) {
    throw new Error(`geometry has no anchor for port '${portKey(port)}'`)
  }
  return add(center, local)
}

export function nodeGeometry(d: Diagram, id: NodeId): NodeGeometry {
  const n = d.nodes[id]
  if (n === undefined) throw new Error(`unknown node '${id}'`)
  // Return-typed switch (no default): a new node kind forces its geometry here.
  switch (n.kind) {
    case 'term':
      return bendGrid(trompGrid(n.term))
    case 'atom': {
      const binder = d.regions[n.binder]!
      return atomGeometry(binder.kind === 'bubble' ? binder.arity : 0)
    }
    case 'ref':
      // arg ports only, arity read inline; defId label lands in Task 3.
      return atomGeometry(n.arity)
  }
}

/**
 * Derive the full scene from the diagram and the physics-owned node
 * positions — the ONLY layout state in the system. Region circles are
 * computed bottom-up to enclose their contents plus padding; wires are stars
 * through their endpoint anchors. Pure: same inputs, same scene.
 */
export function buildScene(d: Diagram, positions: ReadonlyMap<NodeId, Vec2>): Scene {
  for (const id of positions.keys()) {
    if (d.nodes[id] === undefined) throw new Error(`position for unknown node '${id}'`)
  }
  const geometries = new Map<NodeId, NodeGeometry>()
  const centers = new Map<NodeId, Vec2>()
  for (const id of Object.keys(d.nodes)) {
    const pos = positions.get(id)
    if (pos === undefined) throw new Error(`no position for node '${id}'`)
    geometries.set(id, nodeGeometry(d, id))
    centers.set(id, pos)
  }

  // region circles, children-first (bottom-up over the region tree)
  const children = new Map<RegionId, RegionId[]>()
  for (const id of Object.keys(d.regions)) children.set(id, [])
  for (const [id, r] of Object.entries(d.regions)) {
    if (r.kind !== 'sheet') children.get(r.parent)!.push(id)
  }
  const nodesIn = new Map<RegionId, NodeId[]>()
  for (const id of Object.keys(d.regions)) nodesIn.set(id, [])
  for (const [id, n] of Object.entries(d.nodes)) nodesIn.get(n.region)!.push(id)

  const circles = new Map<RegionId, { center: Vec2; radius: number }>()
  const computeCircle = (id: RegionId): { center: Vec2; radius: number } => {
    const cached = circles.get(id)
    if (cached !== undefined) return cached
    const content: { center: Vec2; radius: number }[] = [
      ...nodesIn.get(id)!.map((n) => ({ center: centers.get(n)!, radius: geometries.get(n)!.outerRadius })),
      ...children.get(id)!.map((c) => computeCircle(c)),
    ]
    let circle: { center: Vec2; radius: number }
    if (content.length === 0) {
      circle = { center: vec(0, 0), radius: REGION_PADDING }
    } else {
      let center = vec(0, 0)
      for (const c of content) center = add(center, c.center)
      center = scale(center, 1 / content.length)
      const radius = Math.max(...content.map((c) => length(sub(c.center, center)) + c.radius)) + REGION_PADDING
      circle = { center, radius }
    }
    circles.set(id, circle)
    return circle
  }
  for (const id of Object.keys(d.regions)) computeCircle(id)

  const regions: SceneRegion[] = Object.entries(d.regions).map(([id, r]) => ({
    id,
    kind: r.kind,
    center: circles.get(id)!.center,
    radius: circles.get(id)!.radius,
    shaded: polarity(d, id) === 'negative',
  }))

  const nodes: SceneNode[] = Object.keys(d.nodes).map((id) => ({
    id,
    center: centers.get(id)!,
    geometry: geometries.get(id)!,
  }))

  const wires: SceneWire[] = Object.entries(d.wires).map(([id, w]) => {
    const spokes = w.endpoints.map((ep) => anchorOf(geometries.get(ep.node)!, centers.get(ep.node)!, ep.port))
    let hub: Vec2
    if (spokes.length === 0) {
      hub = circles.get(w.scope)!.center
    } else {
      let c = vec(0, 0)
      for (const s of spokes) c = add(c, s)
      hub = scale(c, 1 / spokes.length)
    }
    return { id, hub, spokes }
  })

  return { regions, nodes, wires }
}
