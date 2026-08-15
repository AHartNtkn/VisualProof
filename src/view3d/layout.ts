import type { NodeId, RegionId } from '../kernel/diagram/diagram'
import type { DiagramSpec, SceneItem, Terminal } from './spec'
import {
  add3, cross3, dist3, dot3, len3, norm3, scale3, sub3, v3, type Vec3,
} from './vec3'

export const UNIT = 1
export const CLEARANCE = 0.3 * UNIT
export const BRANCH_ANGLE = 0.6
export const AZ_GAP = 0.12
export const RING_MIN_R = 0.25 * UNIT
export const PORT_ARC = 0.35 * UNIT
export const TIP_PAD = 0.5 * UNIT

export const ringRadius = (portCount: number): number =>
  Math.max(RING_MIN_R, (portCount * PORT_ARC) / (2 * Math.PI))

export type PlacedRegion = {
  region: RegionId
  base: Vec3
  tip: Vec3
  dir: Vec3
  ref: Vec3
  contentStart: number
}
export type PlacedRing = {
  node: NodeId
  center: Vec3
  axis: Vec3
  radius: number
  anchors: Map<string, Vec3>
}
export type TreeLayout = {
  regions: Map<RegionId, PlacedRegion>
  beads: { region: RegionId; pos: Vec3 }[]
  identityAnchor: Map<NodeId, Vec3>
  rings: Map<NodeId, PlacedRing>
  spheres: Map<RegionId, { center: Vec3; r: number }>
  anchorOf(t: Terminal): Vec3
}

const DELTA = CLEARANCE

type ChildPlan = { region: RegionId; t: number; tilt: number; azimuth: number; stem: number }
type Summary = {
  segLen: number
  corridorR: number
  itemT: Map<string, number>       // item key (node id or child region id) → offset
  children: ChildPlan[]
  c: number                        // enclosing-sphere center along own axis from content start
  rho: number
}

const itemKey = (i: SceneItem): string => (i.kind === 'node' ? i.id : i.region)

/** 1D convex minimization of f over [lo, hi] by ternary search. */
function argminTernary(f: (t: number) => number, lo: number, hi: number): number {
  let a = lo, b = hi
  for (let i = 0; i < 200; i++) {
    const m1 = a + (b - a) / 3, m2 = b - (b - a) / 3
    if (f(m1) <= f(m2)) b = m2
    else a = m1
  }
  return (a + b) / 2
}

export function layoutTree(spec: DiagramSpec): TreeLayout {
  // wire endpoints per node (identity spacing input)
  const endpointCount = new Map<NodeId, number>()
  for (const w of spec.wires) for (const t of w.terminals) {
    endpointCount.set(t.node, (endpointCount.get(t.node) ?? 0) + 1)
  }
  const portCountOf = (id: NodeId): number => spec.nodes.get(id)!.portKeys.length
  const spacingOf = (item: SceneItem): number => {
    if (item.kind === 'branch') return 2 * DELTA + DELTA * spec.escapes.get(item.region)!
    const n = spec.nodes.get(item.id)!
    if (n.kind === 'identity') return 2 * DELTA + DELTA * (endpointCount.get(item.id) ?? 0)
    return 2 * ringRadius(portCountOf(item.id)) + 2 * DELTA
  }

  // ---- bottom-up summaries ----
  const summaries = new Map<RegionId, Summary>()
  const summarize = (rid: RegionId): Summary => {
    const rs = spec.regions.get(rid)!
    const childSummaries = new Map<RegionId, Summary>()
    for (const item of rs.items) if (item.kind === 'branch') childSummaries.set(item.region, summarize(item.region))

    const itemT = new Map<string, number>()
    let acc = 0
    for (const item of rs.items) {
      const s = spacingOf(item)
      itemT.set(itemKey(item), acc + s / 2)
      acc += s
    }
    const segLen = acc + TIP_PAD
    let maxRingR = 0
    for (const item of rs.items) {
      if (item.kind === 'node' && spec.nodes.get(item.id)!.kind !== 'identity') {
        maxRingR = Math.max(maxRingR, ringRadius(portCountOf(item.id)))
      }
    }
    const corridorR = DELTA * (1 + spec.escapes.get(rid)!) + maxRingR

    const branchItems = rs.items.filter((i): i is Extract<SceneItem, { kind: 'branch' }> => i.kind === 'branch')
    const loneChain = rs.items.length === 1 && branchItems.length === 1
    const children: ChildPlan[] = []
    if (loneChain) {
      const child = branchItems[0]!
      children.push({ region: child.region, t: itemT.get(child.region)!, tilt: 0, azimuth: 0, stem: 2 * DELTA })
    } else if (branchItems.length > 0) {
      const tilt = BRANCH_ANGLE
      const baseStem = branchItems.map((bi) => {
        const cs = childSummaries.get(bi.region)!
        return Math.max(2 * DELTA, (corridorR + cs.rho + DELTA) / Math.sin(tilt) - cs.c)
      })
      const demands = (k: number): number[] => branchItems.map((bi, i) => {
        const cs = childSummaries.get(bi.region)!
        const d = (k * baseStem[i]! + cs.c) * Math.sin(tilt)
        const beta = Math.asin(Math.min(1, (cs.rho + DELTA / 2) / d))
        return 2 * beta + AZ_GAP + (DELTA * spec.escapes.get(bi.region)!) / d
      })
      const total = (k: number): number => demands(k).reduce((a, b) => a + b, 0)
      let k = 1
      if (total(1) > 2 * Math.PI) {
        let lo = 1, hi = 1e6
        if (total(hi) > 2 * Math.PI) throw new Error(`layout: region ${rid} cannot fit ${branchItems.length} child cones azimuthally`)
        for (let i = 0; i < 80; i++) {
          const mid = (lo + hi) / 2
          if (total(mid) > 2 * Math.PI) lo = mid
          else hi = mid
        }
        k = hi
      }
      const w = demands(k)
      let az = 0
      branchItems.forEach((bi, i) => {
        children.push({
          region: bi.region, t: itemT.get(bi.region)!, tilt,
          azimuth: az + w[i]! / 2, stem: k * baseStem[i]!,
        })
        az += w[i]!
      })
    }

    // enclosing sphere: center on own axis (local: origin = content start, axis = +z)
    const localChildCenter = (cp: ChildPlan): Vec3 => {
      const cs = childSummaries.get(cp.region)!
      const reach = cp.stem + cs.c
      return v3(
        Math.sin(cp.tilt) * reach * Math.cos(cp.azimuth),
        Math.sin(cp.tilt) * reach * Math.sin(cp.azimuth),
        cp.t + Math.cos(cp.tilt) * reach,
      )
    }
    const f = (ct: number): number => {
      let m = Math.max(Math.hypot(ct, corridorR), Math.hypot(segLen - ct, corridorR))
      for (const cp of children) {
        const cs = childSummaries.get(cp.region)!
        m = Math.max(m, dist3(localChildCenter(cp), v3(0, 0, ct)) + cs.rho)
      }
      return m
    }
    let reachMax = segLen
    for (const cp of children) reachMax = Math.max(reachMax, cp.t + cp.stem + childSummaries.get(cp.region)!.c + childSummaries.get(cp.region)!.rho)
    const c = argminTernary(f, -reachMax, 2 * reachMax)
    const summary: Summary = { segLen, corridorR, itemT, children, c, rho: f(c) }
    summaries.set(rid, summary)
    return summary
  }
  summarize(spec.root)

  // ---- top-down realization ----
  const regions = new Map<RegionId, PlacedRegion>()
  const beads: { region: RegionId; pos: Vec3 }[] = []
  const identityAnchor = new Map<NodeId, Vec3>()
  const rings = new Map<NodeId, PlacedRing>()
  const spheres = new Map<RegionId, { center: Vec3; r: number }>()
  const nodePrimary = new Map<NodeId, Vec3>()

  const realize = (rid: RegionId, bead: Vec3, dir: Vec3, ref: Vec3, stem: number): void => {
    const s = summaries.get(rid)!
    const start = add3(bead, scale3(dir, stem))
    const tip = add3(start, scale3(dir, s.segLen))
    regions.set(rid, { region: rid, base: bead, tip, dir, ref, contentStart: stem })
    spheres.set(rid, { center: add3(start, scale3(dir, s.c)), r: s.rho })
    const rs = spec.regions.get(rid)!
    for (const item of rs.items) {
      if (item.kind !== 'node') continue
      const pos = add3(start, scale3(dir, s.itemT.get(item.id)!))
      nodePrimary.set(item.id, pos)
      const n = spec.nodes.get(item.id)!
      if (n.kind === 'identity') identityAnchor.set(item.id, pos)
      else rings.set(item.id, { node: item.id, center: pos, axis: dir, radius: ringRadius(n.portKeys.length), anchors: new Map() })
    }
    const n2 = norm3(cross3(dir, ref))
    for (const cp of s.children) {
      const childBead = add3(start, scale3(dir, cp.t))
      beads.push({ region: cp.region, pos: childBead })
      const w = add3(scale3(ref, Math.cos(cp.azimuth)), scale3(n2, Math.sin(cp.azimuth)))
      const childDir = cp.tilt === 0 ? dir : norm3(add3(scale3(dir, Math.cos(cp.tilt)), scale3(w, Math.sin(cp.tilt))))
      const parallel = sub3(dir, scale3(childDir, dot3(dir, childDir)))
      const childRef = len3(parallel) < 1e-9 ? ref : norm3(parallel)
      realize(cp.region, childBead, childDir, childRef, cp.stem)
    }
  }
  realize(spec.root, v3(0, 0, 0), v3(0, 1, 0), v3(1, 0, 0), 0)

  // ---- ring rotations: circular mean of partner directions ----
  const partnersOf = new Map<NodeId, Vec3[]>()
  for (const w of spec.wires) {
    for (const t of w.terminals) {
      for (const o of w.terminals) {
        if (o.node === t.node) continue
        const p = nodePrimary.get(o.node)
        if (p !== undefined) {
          const list = partnersOf.get(t.node) ?? []
          list.push(p)
          partnersOf.set(t.node, list)
        }
      }
    }
  }
  for (const ring of rings.values()) {
    const pr = regions.get(spec.nodes.get(ring.node)!.region)!
    const n1 = pr.ref
    const n2 = norm3(cross3(ring.axis, n1))
    let m = v3(0, 0, 0)
    for (const p of partnersOf.get(ring.node) ?? []) {
      const rel = sub3(p, ring.center)
      const proj = sub3(rel, scale3(ring.axis, dot3(rel, ring.axis)))
      const l = len3(proj)
      if (l > 1e-9) m = add3(m, scale3(proj, 1 / l))
    }
    const theta0 = len3(m) < 1e-9 ? 0 : Math.atan2(dot3(m, n2), dot3(m, n1))
    const keys = spec.nodes.get(ring.node)!.portKeys
    keys.forEach((pk, i) => {
      const a = theta0 + (2 * Math.PI * i) / keys.length
      ring.anchors.set(pk, add3(ring.center, add3(
        scale3(n1, ring.radius * Math.cos(a)),
        scale3(n2, ring.radius * Math.sin(a)),
      )))
    })
  }

  const anchorOf = (t: Terminal): Vec3 => {
    const ia = identityAnchor.get(t.node)
    if (ia !== undefined) return ia
    const ring = rings.get(t.node)
    if (ring === undefined) throw new Error(`layout: no anchor host for node ${t.node}`)
    const a = ring.anchors.get(t.portKey)
    if (a === undefined) throw new Error(`layout: node ${t.node} has no port ${t.portKey}`)
    return a
  }
  return { regions, beads, identityAnchor, rings, spheres, anchorOf }
}
