import type { Entity, Scene3 } from './scene'
import { add3, dist3, lerp3, scale3, type Vec3 } from './vec3'

export type FadedEntity = Entity & { alpha?: number }
export type TweenPlan = {
  moves: { from: Entity; to: Entity }[]
  enters: Entity[]
  exits: Entity[]
  fromBounds: { center: Vec3; radius: number }
  toBounds: { center: Vec3; radius: number }
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

export function planTransition(prev: Scene3, next: Scene3): TweenPlan {
  const prevByKey = new Map(prev.entities.map((e) => [e.key, e]))
  const nextByKey = new Map(next.entities.map((e) => [e.key, e]))
  const moves: { from: Entity; to: Entity }[] = []
  const enters: Entity[] = []
  const exits: Entity[] = []
  for (const e of next.entities) {
    const p = prevByKey.get(e.key)
    if (p === undefined) { enters.push(e); continue }
    if (hasPts(p) && hasPts(e)) {
      const m = Math.max(p.pts.length, e.pts.length)
      moves.push({ from: { ...p, pts: resample(p.pts, m) }, to: { ...e, pts: resample(e.pts, m) } })
    } else {
      moves.push({ from: p, to: e })
    }
  }
  for (const p of prev.entities) if (!nextByKey.has(p.key)) exits.push(p)
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
