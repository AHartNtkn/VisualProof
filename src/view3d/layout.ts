import type { NodeId, RegionId } from '../kernel/diagram/diagram'
import type { DiagramSpec, SceneItem, Terminal } from './spec'
import {
  add3, cross3, dist3, dot3, len3, norm3, scale3, segSegDist, sub3, v3, type Vec3,
} from './vec3'

export const UNIT = 1
export const CLEARANCE = 0.3 * UNIT
export const BRANCH_ANGLE = 0.6
export const AZ_GAP = 0.12
// A ring's center sits ON its own region's branch axis, so a rim anchor's
// distance to that branch is exactly the ring's radius. Wires terminate at
// rim anchors, so the radius must clear the branch by at least CLEARANCE, or
// every low-arity node's own wire terminal would sit inside its own
// region's clearance envelope by construction — unroutable no matter how
// the wire is pushed, since the violating endpoint itself never moves.
export const RING_MIN_R = CLEARANCE + 0.1 * UNIT
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
  identityAnchor: Map<NodeId, Vec3>
  rings: Map<NodeId, PlacedRing>
  spheres: Map<RegionId, { center: Vec3; r: number }>
  anchorOf(t: Terminal): Vec3
}

const DELTA = CLEARANCE

type ChildPlan = { region: RegionId; t: number; tilt: number; azimuth: number; stem: number }
/** A capsule in a region's local frame (origin = content start, +z = axis,
    +x = azimuth-0 reference). */
type LCap = { a: Vec3; b: Vec3; r: number }
type Summary = {
  segLen: number
  corridorR: number
  itemT: Map<string, number>       // node id → offset along the line
  children: ChildPlan[]
  /** The subtree's true content envelope: its own corridor capsule plus
      every descendant's, transformed into this frame. Stems and azimuth
      footprints measure against THIS — a single axis-centered sphere balloons
      behind a wide fan and forces subtree-sized bare stems. */
  caps: LCap[]
  c: number                        // enclosing-sphere center along own axis (summary export only)
  rho: number
}

/** Child frame axes expressed in the parent's local frame, for a branch at
    tilt φ from the parent axis and azimuth α about it. Matches realize()'s
    world-space construction exactly (ez = child dir; ex = child ref). */
function childFrame(tilt: number, azimuth: number): { ex: Vec3; ey: Vec3; ez: Vec3 } {
  const ez = v3(Math.sin(tilt) * Math.cos(azimuth), Math.sin(tilt) * Math.sin(azimuth), Math.cos(tilt))
  const ex = tilt === 0
    ? v3(1, 0, 0)
    : norm3(v3(-Math.cos(tilt) * Math.cos(azimuth), -Math.cos(tilt) * Math.sin(azimuth), Math.sin(tilt)))
  return { ex, ey: cross3(ez, ex), ez }
}

/** Map a child-local point into the parent's local frame: attach at z = t on
    the parent axis, advance `stem` along the child axis, then rotate. */
function intoParent(p: Vec3, t: number, stem: number, F: { ex: Vec3; ey: Vec3; ez: Vec3 }): Vec3 {
  return add3(
    v3(0, 0, t),
    add3(
      scale3(F.ez, stem + p.z),
      add3(scale3(F.ex, p.x), scale3(F.ey, p.y)),
    ),
  )
}

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
  const spacingOf = (id: NodeId): number => {
    const n = spec.nodes.get(id)!
    if (n.kind === 'identity') return 2 * DELTA + DELTA * (endpointCount.get(id) ?? 0)
    return 2 * ringRadius(portCountOf(id)) + 2 * DELTA
  }

  // ---- bottom-up summaries ----
  const summaries = new Map<RegionId, Summary>()
  const summarize = (rid: RegionId): Summary => {
    const rs = spec.regions.get(rid)!
    const childSummaries = new Map<RegionId, Summary>()
    for (const item of rs.items) if (item.kind === 'branch') childSummaries.set(item.region, summarize(item.region))

    // The line carries ONLY the region's nodes (USER ruling 2026-08-15):
    // sibling sub-cuts never compete for room along the parent's axis, so
    // spreading them there only made the tree tall. All children fan from
    // the segment TIP instead; a childless line keeps a short bare tail so
    // it still reads as a line, while a parented line ends exactly at its
    // fan point (no spike past the last node).
    const itemT = new Map<string, number>()
    let acc = 0
    for (const item of rs.items) {
      if (item.kind !== 'node') continue
      const s = spacingOf(item.id)
      itemT.set(item.id, acc + s / 2)
      acc += s
    }
    const branchItems = rs.items.filter((i): i is Extract<SceneItem, { kind: 'branch' }> => i.kind === 'branch')
    const segLen = acc + (branchItems.length > 0 ? 0 : TIP_PAD)
    let maxRingR = 0
    for (const item of rs.items) {
      if (item.kind === 'node' && spec.nodes.get(item.id)!.kind !== 'identity') {
        maxRingR = Math.max(maxRingR, ringRadius(portCountOf(item.id)))
      }
    }
    const corridorR = DELTA * (1 + spec.escapes.get(rid)!) + maxRingR

    const ownCorridor: LCap = { a: v3(0, 0, 0), b: v3(0, 0, segLen), r: corridorR }
    const capsAt = (region: RegionId, tilt: number, azimuth: number, stem: number): LCap[] => {
      const F = childFrame(tilt, azimuth)
      return childSummaries.get(region)!.caps.map((cp) => ({
        a: intoParent(cp.a, segLen, stem, F),
        b: intoParent(cp.b, segLen, stem, F),
        r: cp.r,
      }))
    }
    const clearOfCorridor = (caps: readonly LCap[]): boolean =>
      caps.every((cp) => segSegDist(cp.a, cp.b, ownCorridor.a, ownCorridor.b) >= cp.r + corridorR + DELTA * (1 - 1e-9))

    const children: ChildPlan[] = []
    if (branchItems.length === 1) {
      // A single sub-cut continues the line collinearly; the polarity color
      // change alone marks the crossing (USER ruling 2026-08-16).
      children.push({ region: branchItems[0]!.region, t: segLen, tilt: 0, azimuth: 0, stem: 2 * DELTA })
    } else if (branchItems.length > 1) {
      // Minimal clearance stem per child at a given tilt, against the TRUE
      // content envelope. The sphere-based (corridorR+rho+δ)/sinφ − c stem
      // keeps every content point radially clear of the corridor by
      // construction, so it brackets the bisection from above; the capsule
      // test then shrinks the bare lead-in to what the content actually
      // needs (monotone: every capsule point's corridor distance grows
      // with the stem, its direction having a positive radial component).
      const stemFor = (region: RegionId, tilt: number): number => {
        const cs = childSummaries.get(region)!
        let hi = Math.max(2 * DELTA, (corridorR + cs.rho + DELTA) / Math.sin(tilt) - cs.c)
        if (clearOfCorridor(capsAt(region, tilt, 0, 2 * DELTA))) return 2 * DELTA
        let lo = 2 * DELTA
        for (let i = 0; i < 60; i++) {
          const mid = (lo + hi) / 2
          if (clearOfCorridor(capsAt(region, tilt, 0, mid))) hi = mid
          else lo = mid
        }
        return hi
      }
      // Azimuthal footprint of one child from the fan point: for every
      // capsule end-sphere, its azimuth offset from the child's own azimuth
      // plus the half-angle its δ/2-inflated radius subtends at its radial
      // distance from the parent axis. Disjoint azimuth wedges each holding
      // their child's inflated capsules keep siblings ≥ δ apart.
      const footprint = (region: RegionId, tilt: number, stem: number): { width: number; minRadial: number } => {
        const caps = capsAt(region, tilt, 0, stem)
        let width = 0
        let minRadial = Infinity
        for (const cp of caps) {
          for (const e of [cp.a, cp.b]) {
            const radial = Math.hypot(e.x, e.y)
            minRadial = Math.min(minRadial, Math.max(radial, 1e-9))
            const off = Math.abs(Math.atan2(e.y, e.x))
            const half = Math.asin(Math.min(1, (cp.r + DELTA / 2) / Math.max(radial, cp.r + DELTA / 2)))
            width = Math.max(width, off + half)
          }
        }
        return { width, minRadial }
      }
      const demands = (tilt: number, k: number): number[] => branchItems.map((bi) => {
        const fp = footprint(bi.region, tilt, k * stemFor(bi.region, tilt))
        return 2 * fp.width + AZ_GAP + (DELTA * spec.escapes.get(bi.region)!) / fp.minRadial
      })
      const total = (tilt: number, k: number): number =>
        demands(tilt, k).reduce((a, b) => a + b, 0)
      // Azimuthal overflow resolves ANGULARLY first: widening the tilt
      // toward a flat fan grows the room between siblings without a
      // millimetre of extra bare stem — heavy boughs spread flatter. Only
      // when even a perpendicular fan cannot fit do stems scale. The tilt
      // scan is a fixed grid (its objective is not provably monotone); the
      // stem scale is a monotone bisection.
      const TILT_STEPS = 64
      let tilt = BRANCH_ANGLE
      let k = 1
      if (total(tilt, 1) > 2 * Math.PI) {
        let found = false
        for (let i = 1; i <= TILT_STEPS; i++) {
          const cand = BRANCH_ANGLE + ((Math.PI / 2 - BRANCH_ANGLE) * i) / TILT_STEPS
          if (total(cand, 1) <= 2 * Math.PI) { tilt = cand; found = true; break }
        }
        if (!found) {
          tilt = Math.PI / 2
          let lo = 1, hi = 1e6
          if (total(tilt, hi) > 2 * Math.PI) throw new Error(`layout: region ${rid} cannot fit ${branchItems.length} child cones azimuthally`)
          for (let i = 0; i < 80; i++) {
            const mid = (lo + hi) / 2
            if (total(tilt, mid) > 2 * Math.PI) lo = mid
            else hi = mid
          }
          k = hi
        }
      }
      const w = demands(tilt, k)
      let az = 0
      branchItems.forEach((bi, i) => {
        children.push({
          region: bi.region, t: segLen, tilt,
          azimuth: az + w[i]! / 2, stem: k * stemFor(bi.region, tilt),
        })
        az += w[i]!
      })
    }

    // The subtree's capsule envelope: own corridor plus every child's caps
    // in their placed pose.
    const caps: LCap[] = [ownCorridor]
    for (const cp of children) {
      const F = childFrame(cp.tilt, cp.azimuth)
      for (const cc of childSummaries.get(cp.region)!.caps) {
        caps.push({ a: intoParent(cc.a, cp.t, cp.stem, F), b: intoParent(cc.b, cp.t, cp.stem, F), r: cc.r })
      }
    }

    // Enclosing sphere (summary export for camera fit and nesting tests):
    // smallest axis-centered sphere containing the capsule envelope.
    const f = (ct: number): number => {
      let m = 0
      const q = (z: number): Vec3 => v3(0, 0, z)
      for (const cp of caps) m = Math.max(m, Math.max(dist3(cp.a, q(ct)), dist3(cp.b, q(ct))) + cp.r)
      return m
    }
    let reachMax = segLen
    for (const cp of caps) reachMax = Math.max(reachMax, len3(cp.a) + cp.r, len3(cp.b) + cp.r)
    const c = argminTernary(f, -reachMax, 2 * reachMax)
    const summary: Summary = { segLen, corridorR, itemT, children, caps, c, rho: f(c) }
    summaries.set(rid, summary)
    return summary
  }
  summarize(spec.root)

  // ---- top-down realization ----
  const regions = new Map<RegionId, PlacedRegion>()
  const identityAnchor = new Map<NodeId, Vec3>()
  const rings = new Map<NodeId, PlacedRing>()
  const spheres = new Map<RegionId, { center: Vec3; r: number }>()
  const nodePrimary = new Map<NodeId, Vec3>()

  const realize = (rid: RegionId, base: Vec3, dir: Vec3, ref: Vec3, stem: number): void => {
    const s = summaries.get(rid)!
    const start = add3(base, scale3(dir, stem))
    const tip = add3(start, scale3(dir, s.segLen))
    regions.set(rid, { region: rid, base, tip, dir, ref, contentStart: stem })
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
      const childBase = add3(start, scale3(dir, cp.t))
      const w = add3(scale3(ref, Math.cos(cp.azimuth)), scale3(n2, Math.sin(cp.azimuth)))
      const childDir = cp.tilt === 0 ? dir : norm3(add3(scale3(dir, Math.cos(cp.tilt)), scale3(w, Math.sin(cp.tilt))))
      const parallel = sub3(dir, scale3(childDir, dot3(dir, childDir)))
      const childRef = len3(parallel) < 1e-9 ? ref : norm3(parallel)
      realize(cp.region, childBase, childDir, childRef, cp.stem)
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
  return { regions, identityAnchor, rings, spheres, anchorOf }
}
