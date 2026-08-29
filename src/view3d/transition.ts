import type { Entity, Scene3 } from './scene'
import { add3, dist3, lerp3, scale3, segClosest, type Vec3 } from './vec3'

export type FadedEntity = Entity & { alpha?: number }
export type TweenPlan = {
  moves: { from: Entity; to: Entity }[]
  enters: Entity[]
  exits: Entity[]
  fromBounds: { center: Vec3; radius: number }
  toBounds: { center: Vec3; radius: number }
}

export const SCENE_TWEEN_MS = 350

export class SceneTweenTrack {
  private plan: TweenPlan
  private startedAt: number
  private targetScene: Scene3

  public constructor(displayed: Scene3, target: Scene3, now: number) {
    this.plan = planTransition(displayed, target)
    this.targetScene = target
    this.startedAt = now
  }

  public get target(): Scene3 {
    return this.targetScene
  }

  public begin(displayed: Scene3, target: Scene3, now: number): this {
    this.plan = planTransition(displayed, target)
    this.targetScene = target
    this.startedAt = now
    return this
  }

  public sample(now: number): Scene3 {
    if (this.completed(now)) return this.targetScene
    return sceneAt(this.plan, this.progress(now))
  }

  public completed(now: number): boolean {
    return this.progress(now) === 1
  }

  private progress(now: number): number {
    return Math.max(0, Math.min(1, (now - this.startedAt) / SCENE_TWEEN_MS))
  }
}

/** Arc-length-uniform resampling; endpoints exact. */
export function resample(pts: Vec3[], m: number): Vec3[] {
  if (pts.length === 0) throw new Error('resample: empty polyline')
  if (m < 2) throw new Error('resample: need m ≥ 2')
  const cum: number[] = [0]
  for (let i = 1; i < pts.length; i++) cum.push(cum[i - 1]! + dist3(pts[i - 1]!, pts[i]!))
  const total = cum[cum.length - 1]!
  if (total === 0) return Array.from({ length: m }, () => pts[0]!)
  const out: Vec3[] = []
  let seg = 1
  for (let k = 0; k < m; k++) {
    const target = (total * k) / (m - 1)
    while (seg < pts.length - 1 && cum[seg]! < target) seg++
    const span = cum[seg]! - cum[seg - 1]!
    const t = span === 0 ? 0 : (target - cum[seg - 1]!) / span
    out.push(lerp3(pts[seg - 1]!, pts[seg]!, t))
  }
  return out
}

const hasPts = (e: Entity): e is Extract<Entity, { pts: Vec3[] }> => 'pts' in e
const isStrand = (e: Entity): e is Extract<Entity, { kind: 'strand' }> => e.kind === 'strand'

/** Closest point to `p` on any of the given polylines. */
function projectOntoPolylines(p: Vec3, polys: readonly (readonly Vec3[])[]): Vec3 {
  let best = polys[0]![0]!
  let bestD = Infinity
  for (const pts of polys) {
    for (let i = 1; i < pts.length; i++) {
      const c = segClosest(p, pts[i - 1]!, pts[i]!)
      const d = dist3(p, c)
      if (d < bestD) { bestD = d; best = c }
    }
    if (pts.length === 1) {
      const d = dist3(p, pts[0]!)
      if (d < bestD) { bestD = d; best = pts[0]! }
    }
  }
  return best
}

export function planTransition(prev: Scene3, next: Scene3): TweenPlan {
  const moves: { from: Entity; to: Entity }[] = []
  const enters: Entity[] = []
  const exits: Entity[] = []

  // Strands morph at the WIRE level: a proof step reshuffles a wire's edge
  // decomposition, so strand keys pair unrelated segments — the wire is the
  // persistent object. Every strand of the persisting wire's NEW state
  // starts from its projection onto the wire's OLD geometry and deforms
  // outward, so at t=0 the union of strands reads as the old shape and the
  // wire visibly slides into its new one. Fades happen only when the wire
  // itself appears or disappears.
  const strandsByWire = (s: Scene3): Map<string, Extract<Entity, { kind: 'strand' }>[]> => {
    const out = new Map<string, Extract<Entity, { kind: 'strand' }>[]>()
    for (const e of s.entities) {
      if (!isStrand(e)) continue
      const list = out.get(e.wire) ?? []
      list.push(e)
      out.set(e.wire, list)
    }
    return out
  }
  const prevWires = strandsByWire(prev)
  const nextWires = strandsByWire(next)
  for (const [wire, strands] of nextWires) {
    const old = prevWires.get(wire)
    if (old === undefined) {
      enters.push(...strands)
      continue
    }
    const oldPolys = old.map((e) => e.pts)
    for (const e of strands) {
      const from: Entity = { ...e, pts: e.pts.map((p) => projectOntoPolylines(p, oldPolys)) }
      moves.push({ from, to: e })
    }
  }
  for (const [wire, strands] of prevWires) {
    if (!nextWires.has(wire)) exits.push(...strands)
  }

  // Everything else keeps identity by key.
  const prevByKey = new Map(prev.entities.filter((e) => !isStrand(e)).map((e) => [e.key, e]))
  const nextByKey = new Map(next.entities.filter((e) => !isStrand(e)).map((e) => [e.key, e]))
  for (const [key, e] of nextByKey) {
    const p = prevByKey.get(key)
    if (p === undefined) { enters.push(e); continue }
    if (hasPts(p) && hasPts(e)) {
      const m = Math.max(p.pts.length, e.pts.length)
      moves.push({ from: { ...p, pts: resample(p.pts, m) }, to: { ...e, pts: resample(e.pts, m) } })
    } else {
      moves.push({ from: p, to: e })
    }
  }
  for (const [key, p] of prevByKey) if (!nextByKey.has(key)) exits.push(p)
  return {
    moves, enters, exits,
    fromBounds: { center: prev.center, radius: prev.radius },
    toBounds: { center: next.center, radius: next.radius },
  }
}

export function sceneAt(plan: TweenPlan, t: number): { entities: FadedEntity[]; center: Vec3; radius: number } {
  const e = t * t * (3 - 2 * t) // smoothstep
  const entities: FadedEntity[] = []
  for (const mv of plan.moves) {
    if (hasPts(mv.from) && hasPts(mv.to)) {
      entities.push({ ...mv.to, pts: mv.from.pts.map((p, i) => lerp3(p, (mv.to as Extract<Entity, { pts: Vec3[] }>).pts[i]!, e)) })
    } else if ('pos' in mv.from && 'pos' in mv.to) {
      entities.push({ ...mv.to, pos: lerp3((mv.from as Extract<Entity, { pos: Vec3 }>).pos, (mv.to as Extract<Entity, { pos: Vec3 }>).pos, e) })
    } else {
      throw new Error(`transition: key ${mv.from.key} changed entity shape`)
    }
  }
  for (const x of plan.exits) entities.push({ ...x, alpha: 1 - e })
  for (const n of plan.enters) entities.push({ ...n, alpha: e })
  return {
    entities,
    center: add3(scale3(plan.fromBounds.center, 1 - e), scale3(plan.toBounds.center, e)),
    radius: plan.fromBounds.radius * (1 - e) + plan.toBounds.radius * e,
  }
}
