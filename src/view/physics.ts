import type { Diagram, NodeId, Region } from '../kernel/diagram/diagram'
import type { Vec2 } from './vec'
import { add, scale, sub, length, vec, polar } from './vec'
import { buildScene } from './scene'

/**
 * The physics layer's entire state: node positions and velocities. Nothing
 * here is semantic and nothing here is ever serialized (the kernel file
 * format cannot express it; the architecture test pins the import direction).
 */
export type PhysicsState = {
  readonly positions: ReadonlyMap<NodeId, Vec2>
  readonly velocities: ReadonlyMap<NodeId, Vec2>
}

/**
 * Force coefficients. These are NOT correctness heuristics: any positive
 * values give a valid equilibrium of the same constraint system (repulsion,
 * wire springs, cohesion, sibling separation); they tune visual pacing only.
 */
export type PhysicsParams = {
  readonly dt: number
  readonly damping: number
  readonly repulsion: number
  readonly minDistance: number
  readonly wireSpring: number
  readonly cohesion: number
  readonly separation: number
  readonly settleSpeed: number
}

export const DEFAULT_PARAMS: PhysicsParams = {
  dt: 0.05,
  damping: 4,
  repulsion: 400,
  minDistance: 4,
  wireSpring: 2,
  cohesion: 0.4,
  separation: 6,
  settleSpeed: 0.05,
}

const GOLDEN = Math.PI * (3 - Math.sqrt(5))

/**
 * Deterministic seeding: nodes spiral out from the origin in id-sorted order.
 * Arbitrary but deterministic and collision-free — the forces own the layout,
 * the seed only has to avoid coincident starts.
 */
export function initialState(d: Diagram): PhysicsState {
  const ids = Object.keys(d.nodes).sort()
  const positions = new Map<NodeId, Vec2>()
  const velocities = new Map<NodeId, Vec2>()
  ids.forEach((id, i) => {
    positions.set(id, polar(i * GOLDEN, 10 + 6 * i))
    velocities.set(id, vec(0, 0))
  })
  return { positions, velocities }
}

export function step(d: Diagram, s: PhysicsState, params: PhysicsParams): PhysicsState {
  const ids = Object.keys(d.nodes).sort()
  const force = new Map<NodeId, Vec2>(ids.map((id) => [id, vec(0, 0)]))
  const addForce = (id: NodeId, f: Vec2): void => {
    force.set(id, add(force.get(id)!, f))
  }
  const at = (id: NodeId): Vec2 => s.positions.get(id)!

  // all-pairs repulsion
  for (let i = 0; i < ids.length; i++) {
    for (let j = i + 1; j < ids.length; j++) {
      const a = ids[i]!
      const b = ids[j]!
      const delta = sub(at(a), at(b))
      const dist = Math.max(length(delta), params.minDistance)
      const dir = dist > 0 ? scale(delta, 1 / dist) : vec(1, 0)
      const f = scale(dir, params.repulsion / (dist * dist))
      addForce(a, f)
      addForce(b, scale(f, -1))
    }
  }

  // wire springs: endpoints pulled toward the wire centroid
  const scene = buildScene(d, s.positions)
  const wireById = new Map(scene.wires.map((w) => [w.id, w]))
  for (const [wid, w] of Object.entries(d.wires)) {
    const star = wireById.get(wid)!
    for (const ep of w.endpoints) {
      const pull = sub(star.hub, at(ep.node))
      addForce(ep.node, scale(pull, params.wireSpring))
    }
  }

  // per-region cohesion toward the content centroid
  const byRegion = new Map<string, NodeId[]>()
  for (const [id, n] of Object.entries(d.nodes)) {
    const list = byRegion.get(n.region) ?? []
    list.push(id)
    byRegion.set(n.region, list)
  }
  for (const members of byRegion.values()) {
    if (members.length < 2) continue
    let c = vec(0, 0)
    for (const m of members) c = add(c, at(m))
    c = scale(c, 1 / members.length)
    for (const m of members) addForce(m, scale(sub(c, at(m)), params.cohesion))
  }

  // sibling-region separation: overlapping derived circles push their contents apart
  const regionsById = new Map(scene.regions.map((r) => [r.id, r]))
  const siblings = new Map<string, string[]>()
  for (const [id, r] of Object.entries(d.regions)) {
    if (r.kind === 'sheet') continue
    const list = siblings.get(r.parent) ?? []
    list.push(id)
    siblings.set(r.parent, list)
  }
  const subtreeNodes = (root: string): NodeId[] => {
    const out: NodeId[] = []
    for (const [id, n] of Object.entries(d.nodes)) {
      let cur: string | null = n.region
      while (cur !== null) {
        if (cur === root) {
          out.push(id)
          break
        }
        const r: Region | undefined = d.regions[cur]
        if (r === undefined) break
        cur = r.kind === 'sheet' ? null : r.parent
      }
    }
    return out
  }
  for (const sibs of siblings.values()) {
    for (let i = 0; i < sibs.length; i++) {
      for (let j = i + 1; j < sibs.length; j++) {
        const ra = regionsById.get(sibs[i]!)!
        const rb = regionsById.get(sibs[j]!)!
        const delta = sub(ra.center, rb.center)
        const dist = Math.max(length(delta), 1e-6)
        const overlap = ra.radius + rb.radius - dist
        if (overlap <= 0) continue
        const dir = scale(delta, 1 / dist)
        const push = scale(dir, params.separation * overlap)
        for (const n of subtreeNodes(sibs[i]!)) addForce(n, push)
        for (const n of subtreeNodes(sibs[j]!)) addForce(n, scale(push, -1))
      }
    }
  }

  // semi-implicit Euler with damping
  const positions = new Map<NodeId, Vec2>()
  const velocities = new Map<NodeId, Vec2>()
  for (const id of ids) {
    const v0 = s.velocities.get(id)!
    const v1 = scale(add(v0, scale(force.get(id)!, params.dt)), Math.max(0, 1 - params.damping * params.dt))
    velocities.set(id, v1)
    positions.set(id, add(at(id), scale(v1, params.dt)))
  }
  return { positions, velocities }
}

export function settled(s: PhysicsState, params: PhysicsParams): boolean {
  for (const v of s.velocities.values()) {
    if (length(v) >= params.settleSpeed) return false
  }
  return true
}

/** Run to settlement under a tick budget; fail loudly when exhausted (fuel honesty). */
export function settle(d: Diagram, s0: PhysicsState, params: PhysicsParams, maxTicks: number): PhysicsState {
  let s = s0
  for (let i = 0; i < maxTicks; i++) {
    s = step(d, s, params)
    if (settled(s, params)) return s
  }
  throw new Error(`physics did not settle within ${maxTicks} ticks (last max speed above ${params.settleSpeed})`)
}
