import type { Entity, Scene3 } from './scene'
import { termEq } from '../kernel/term/term'
import { sampleBetaMotion, type LambdaMotionPlan } from '../view/lambda-motion'
import type { LambdaMotionTransition } from '../view/lambda-transition'
import { lambdaDiagram, type LambdaEntity } from './lambda'
import { add3, dist3, dot3, lerp3, scale3, segClosest, sub3, type Vec3 } from './vec3'

export type FadedEntity = Entity & { alpha?: number }
export type TweenScene = Omit<Scene3, 'entities'> & { entities: FadedEntity[] }
export type TweenPlan = {
  moves: { from: Entity; to: Entity }[]
  enters: Entity[]
  exits: Entity[]
  fromBounds: { center: Vec3; radius: number }
  toBounds: { center: Vec3; radius: number }
  lambdaMoves: LambdaTween[]
}

type LambdaTween = {
  node: string
  region: string
  motion: LambdaMotionPlan
  from: LambdaEntity
  to: LambdaEntity
  fromAlong: number
  toAlong: number
  attachments: LambdaAttachment[]
  baseColor: string
  reverse: boolean
}

type LambdaAttachment = {
  readonly portKey: string
  readonly strandKey: string
  readonly endpoint: 'first' | 'last'
}

export const SCENE_TWEEN_MS = 350

export class SceneTweenTrack {
  private plan: TweenPlan
  private startedAt: number
  private targetScene: Scene3

  public constructor(
    displayed: Scene3,
    target: Scene3,
    now: number,
    lambdaBaseColor = '#000000',
    lambdaTransition: LambdaMotionTransition | null = null,
  ) {
    this.plan = planTransition(displayed, target, lambdaBaseColor, lambdaTransition)
    this.targetScene = target
    this.startedAt = now
  }

  public get target(): Scene3 {
    return this.targetScene
  }

  public begin(
    displayed: Scene3,
    target: Scene3,
    now: number,
    lambdaBaseColor = '#000000',
    lambdaTransition: LambdaMotionTransition | null = null,
  ): this {
    this.plan = planTransition(displayed, target, lambdaBaseColor, lambdaTransition)
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
const isLambda = (e: Entity): e is LambdaEntity => e.kind === 'lambda'

type BranchEntity = Extract<Entity, { kind: 'branch' }>

function branchOf(entities: readonly Entity[], region: string): BranchEntity {
  const branch = entities.find((entity): entity is BranchEntity => (
    entity.kind === 'branch' && entity.key === `b:${region}`
  ))
  if (branch === undefined) throw new Error(`transition: Lambda region ${region} has no incident branch`)
  return branch
}

function polylineFraction(pts: readonly Vec3[], point: Vec3): number {
  let total = 0
  const lengths: number[] = []
  for (let index = 1; index < pts.length; index++) {
    const length = dist3(pts[index - 1]!, pts[index]!)
    lengths.push(length)
    total += length
  }
  if (total === 0) return 0
  let bestDistance = Infinity
  let bestAlong = 0
  let before = 0
  for (let index = 1; index < pts.length; index++) {
    const a = pts[index - 1]!, b = pts[index]!, length = lengths[index - 1]!
    const closest = segClosest(point, a, b)
    const distance = dist3(point, closest)
    if (distance < bestDistance) {
      bestDistance = distance
      const segmentFraction = length === 0 ? 0 : dot3(sub3(closest, a), sub3(b, a)) / (length * length)
      bestAlong = before + segmentFraction * length
    }
    before += length
  }
  return bestAlong / total
}

function pointOnPolyline(pts: readonly Vec3[], fraction: number): Vec3 {
  const lengths: number[] = []
  let total = 0
  for (let index = 1; index < pts.length; index++) {
    const length = dist3(pts[index - 1]!, pts[index]!)
    lengths.push(length)
    total += length
  }
  if (total === 0) return pts[0]!
  const target = Math.max(0, Math.min(1, fraction)) * total
  let before = 0
  for (let index = 1; index < pts.length; index++) {
    const length = lengths[index - 1]!
    if (target <= before + length || index === pts.length - 1) {
      return lerp3(pts[index - 1]!, pts[index]!, length === 0 ? 0 : (target - before) / length)
    }
    before += length
  }
  return pts[pts.length - 1]!
}

function attachmentsTo(
  entities: readonly Entity[],
  anchors: ReadonlyMap<string, Vec3>,
): LambdaAttachment[] {
  const attachments: LambdaAttachment[] = []
  for (const entity of entities) {
    if (!isStrand(entity)) continue
    for (const [portKey, anchor] of anchors) {
      if (dist3(entity.pts[0]!, anchor) < 1e-8) {
        attachments.push({ portKey, strandKey: entity.key, endpoint: 'first' })
      }
      if (dist3(entity.pts[entity.pts.length - 1]!, anchor) < 1e-8) {
        attachments.push({ portKey, strandKey: entity.key, endpoint: 'last' })
      }
    }
  }
  return attachments
}

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

export function planTransition(
  prev: Scene3,
  next: Scene3,
  lambdaBaseColor = '#000000',
  lambdaTransition: LambdaMotionTransition | null = null,
): TweenPlan {
  const moves: { from: Entity; to: Entity }[] = []
  const enters: Entity[] = []
  const exits: Entity[] = []

  const firstLambdaByNode = (entities: readonly Entity[]): Map<string, LambdaEntity> => {
    const out = new Map<string, LambdaEntity>()
    for (const entity of entities) if (isLambda(entity) && !out.has(entity.node)) out.set(entity.node, entity)
    return out
  }
  const previousLambdas = firstLambdaByNode(prev.entities)
  const nextLambdas = firstLambdaByNode(next.entities)
  const lambdaMoves: LambdaTween[] = []
  if (lambdaTransition !== null) {
    const { node, plan: motion, direction } = lambdaTransition
    const from = previousLambdas.get(node)
    const to = nextLambdas.get(node)
    const reverse = direction === 'reverse'
    const expectedFrom = reverse ? motion.target : motion.source
    const expectedTo = reverse ? motion.source : motion.target
    const expectedFromArity = reverse
      ? motion.targetInterfaceArity
      : motion.sourceInterfaceArity
    const expectedToArity = reverse
      ? motion.sourceInterfaceArity
      : motion.targetInterfaceArity
    if (
      from !== undefined
      && to !== undefined
      && termEq(from.term, expectedFrom)
      && termEq(to.term, expectedTo)
      && from.interfaceArity === expectedFromArity
      && to.interfaceArity === expectedToArity
    ) {
      if (from.region !== to.region) throw new Error(`transition: Lambda node ${node} changed incident region`)
      const fromBranch = branchOf(prev.entities, from.region)
      const toBranch = branchOf(next.entities, to.region)
      const targetDiagram = lambdaDiagram({
        node: to.node,
        region: to.region,
        term: to.term,
        interfaceArity: to.interfaceArity,
        center: to.center,
        tangent: to.plane.normal,
        scale: to.scale,
      })
      lambdaMoves.push({
        node,
        region: from.region,
        motion,
        from,
        to,
        fromAlong: polylineFraction(fromBranch.pts, from.center),
        toAlong: polylineFraction(toBranch.pts, to.center),
        attachments: attachmentsTo(next.entities, targetDiagram.anchors),
        baseColor: lambdaBaseColor,
        reverse,
      })
    }
  }
  const structuralLambdaNodes = new Set(lambdaMoves.map(({ node }) => node))

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
  const genericEntity = (entity: Entity): boolean => (
    !isStrand(entity) && !(isLambda(entity) && structuralLambdaNodes.has(entity.node))
  )
  const prevByKey = new Map(prev.entities.filter(genericEntity).map((e) => [e.key, e]))
  const nextByKey = new Map(next.entities.filter(genericEntity).map((e) => [e.key, e]))
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
    lambdaMoves,
  }
}

export function sceneAt(plan: TweenPlan, t: number): TweenScene {
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

  const diagrams = new Map<string, ReturnType<typeof lambdaDiagram>>()
  for (const move of plan.lambdaMoves) {
    const branch = branchOf(entities, move.region)
    const branchTangent = sub3(branch.pts[branch.pts.length - 1]!, branch.pts[0]!)
    const endpoint = t === 0 ? move.from : t === 1 ? move.to : null
    const diagram = lambdaDiagram({
      node: move.node,
      region: move.region,
      term: endpoint?.term ?? move.motion.source,
      interfaceArity: move.from.interfaceArity,
      center: endpoint?.center ?? pointOnPolyline(
        branch.pts,
        move.fromAlong + (move.toAlong - move.fromAlong) * e,
      ),
      tangent: endpoint?.plane.normal ?? branchTangent,
      scale: endpoint?.scale ?? move.from.scale + (move.to.scale - move.from.scale) * e,
      ...(endpoint === null ? {
        frame: sampleBetaMotion(move.motion, move.reverse ? 1 - t : t, move.baseColor),
      } : {}),
    })
    diagrams.set(move.node, diagram)
    entities.push(...diagram.strokes)
  }

  // Structural Lambda anchors and their incident strand endpoints are one
  // moving junction. Generic wire interpolation supplies the curve interior;
  // the sampled Lambda frame supplies the exact connected endpoint.
  for (const move of plan.lambdaMoves) {
    const anchors = diagrams.get(move.node)!.anchors
    for (const attachment of move.attachments) {
      const index = entities.findIndex((entity) => entity.key === attachment.strandKey && isStrand(entity))
      if (index < 0) continue
      const strand = entities[index] as Extract<FadedEntity, { kind: 'strand' }>
      const anchor = anchors.get(attachment.portKey)
      if (anchor === undefined) throw new Error(`transition: moving Lambda has no ${attachment.portKey} anchor`)
      const pts = [...strand.pts]
      pts[attachment.endpoint === 'first' ? 0 : pts.length - 1] = anchor
      entities[index] = { ...strand, pts }
    }
  }
  return {
    entities,
    center: add3(scale3(plan.fromBounds.center, 1 - e), scale3(plan.toBounds.center, e)),
    radius: plan.fromBounds.radius * (1 - e) + plan.toBounds.radius * e,
  }
}
