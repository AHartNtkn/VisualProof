import type { WireId } from '../kernel/diagram/diagram'
import {
  add3, dist3, lerp3, scale3, segPointDist, segSegClosest, segSegDist, sub3, v3, type Vec3,
} from './vec3'

/**
 * Wire routing as ONE optimization with ONE mechanism (USER ruling
 * 2026-08-15, replacing the repair-loop pipeline whose local escapes chose
 * obstacle sides by accident): every wire edge is a SHORTEST CLEAR PATH on
 * a clearance grid, and every free branch vertex sits at the obstacle-aware
 * 1-median of its network neighbors (argmin of summed grid distance
 * fields). Homotopy is therefore chosen by path length globally — a wire
 * cannot spiral a branch it could pass beside, jut into space, or tangle in
 * a congested pocket, because all of those are strictly longer. The only
 * post-passes are verified length descent (taut chords, rounded corners)
 * and a final clearance verification that throws loudly.
 */

/** `g` names the obstacle GROUP a capsule belongs to (a region line, one
    ring with its spokes, one wire's strands…). Exemption licenses whole
    groups: a ball at an anchor licenses every group that passes through the
    meeting zone — a wire coexists with its own ring, not just with the two
    chords nearest its anchor. */
export type Capsule = { a: Vec3; b: Vec3; r: number; g: string }

/** One wire's network to route. Vertex indexing over `edges`:
    `0..anchors.length` are anchors, then `freeJunctionCount` FREE branch
    vertices whose positions THIS router chooses, then the construction-fixed
    vertices (stub tips). */
export type NetIn = {
  id: WireId
  anchors: Vec3[]
  freeJunctionCount: number
  fixedJunctions: Vec3[]
  edges: (readonly [number, number])[]
  /** Construction stubs as [anchorIndex, fixedJunctionIndex] pairs: short
      straight attachment geometry declared as obstacles UP FRONT so no
      earlier wire can invade where a later wire must attach, and drawn AS
      CONSTRUCTED (a straight segment the sizing rules keep legal) rather
      than grid-routed. A fixed junction that merely pins a vertex is not
      construction geometry and does not belong here. */
  stubs: (readonly [number, number])[]
}

const SMOOTH = 0.4

/** One exemption ball: a meeting point (anchor or junction) plus the set of
    obstacle groups that pass through its meeting zone (within δ) — the
    geometry the wire legitimately touches there. */
export type Ball = { e: Vec3; groups: ReadonlySet<string> }
/** A net's license: its own group (its strands always meet themselves at
    shared vertices) plus its exemption balls. */
export type License = { own: string; balls: readonly Ball[] }

/** Whether a sub-δ approach to capsule `c` at position `at` is licensed:
    `at` lies inside some ball whose licensed groups include `c`'s group
    (or `c` belongs to the net's own strands, which meet it at every shared
    vertex). Licensing is per GROUP, never per capsule — a wire's anchor
    licenses its whole ring — and foreign geometry that merely passes near
    the ball stays a stranger the curve must clear. Own strands license
    across the wide ball (edges of one wire share vertices and diverge
    slowly); foreign-but-meeting groups only within the TIGHT ball, so a
    wire may touch its line or ring AT the anchor but never run along it
    (USER law: a wire is never parallel-and-overlapping with a branch). */
const licensedHit = (at: Vec3, c: Capsule, lic: License, delta: number): boolean =>
  lic.balls.some((b) => {
    const d = dist3(at, b.e)
    return c.g === lic.own ? d < 2.5 * delta : d < delta && b.groups.has(c.g)
  })

// ---------------------------------------------------------------------------
// Obstacle broadphase: uniform spatial hash over capsule AABBs
// ---------------------------------------------------------------------------

/** Registration inflates each capsule's AABB by (r + δ + cell), so a point
    query needs only the point's own hash cell and a segment query needs
    only cells of samples spaced cell/2 along it — every capsule within
    (r + δ) of the query is guaranteed to be registered there. Exact
    distances are always re-checked; the hash only prunes. */
class CapsuleIndex {
  readonly caps: Capsule[] = []
  private readonly cell: number
  private readonly delta: number
  private readonly map = new Map<number, number[]>()
  private stampGen = 0
  private stamps: number[] = []

  constructor(delta: number) {
    this.delta = delta
    this.cell = 4 * delta
  }

  private key(ix: number, iy: number, iz: number): number {
    return ((ix * 73856093) ^ (iy * 19349663) ^ (iz * 83492791)) | 0
  }

  push(c: Capsule): void {
    const idx = this.caps.length
    this.caps.push(c)
    this.stamps.push(0)
    const inf = c.r + this.delta + this.cell
    const lo = [Math.min(c.a.x, c.b.x) - inf, Math.min(c.a.y, c.b.y) - inf, Math.min(c.a.z, c.b.z) - inf]
    const hi = [Math.max(c.a.x, c.b.x) + inf, Math.max(c.a.y, c.b.y) + inf, Math.max(c.a.z, c.b.z) + inf]
    const c0 = lo.map((x) => Math.floor(x / this.cell))
    const c1 = hi.map((x) => Math.floor(x / this.cell))
    for (let iz = c0[2]!; iz <= c1[2]!; iz++) for (let iy = c0[1]!; iy <= c1[1]!; iy++) for (let ix = c0[0]!; ix <= c1[0]!; ix++) {
      const k = this.key(ix, iy, iz)
      const list = this.map.get(k)
      if (list === undefined) this.map.set(k, [idx])
      else list.push(idx)
    }
  }

  private collect(k: number, out: number[]): void {
    const list = this.map.get(k)
    if (list === undefined) return
    for (const idx of list) {
      if (this.stamps[idx] === this.stampGen) continue
      this.stamps[idx] = this.stampGen
      out.push(idx)
    }
  }

  nearPoint(p: Vec3): number[] {
    this.stampGen++
    const out: number[] = []
    this.collect(this.key(Math.floor(p.x / this.cell), Math.floor(p.y / this.cell), Math.floor(p.z / this.cell)), out)
    return out
  }

  nearSegment(a: Vec3, b: Vec3): number[] {
    this.stampGen++
    const out: number[] = []
    const n = Math.max(1, Math.ceil(dist3(a, b) / (this.cell / 2)))
    for (let s = 0; s <= n; s++) {
      const p = lerp3(a, b, s / n)
      this.collect(this.key(Math.floor(p.x / this.cell), Math.floor(p.y / this.cell), Math.floor(p.z / this.cell)), out)
    }
    return out
  }
}

/** Capsules the point `p` penetrates (within r + delta). */
function penetrations(p: Vec3, idx: CapsuleIndex, delta: number): Capsule[] {
  const out: Capsule[] = []
  for (const ci of idx.nearPoint(p)) {
    const c = idx.caps[ci]!
    if (segPointDist(p, c.a, c.b) < c.r + delta * (1 - 1e-9)) out.push(c)
  }
  return out
}

/** Obstacle groups passing through the meeting zone of `e` (within δ). */
function groupsNearIdx(e: Vec3, idx: CapsuleIndex, delta: number): Set<string> {
  const out = new Set<string>()
  for (const ci of idx.nearPoint(e)) {
    const c = idx.caps[ci]!
    if (segPointDist(e, c.a, c.b) < c.r + delta) out.add(c.g)
  }
  return out
}

/** Capsules whose clearance is violated by the EDGE [a,b], not just its
    endpoints — the symmetric edge-level invariant. Exemption is evaluated
    at the edge's own closest-approach point to each capsule, which keeps it
    well-defined regardless of sampling density. */
function edgeHits(a: Vec3, b: Vec3, idx: CapsuleIndex, lic: License, delta: number): Capsule[] {
  const out: Capsule[] = []
  for (const ci of idx.nearSegment(a, b)) {
    const c = idx.caps[ci]!
    if (segSegDist(a, b, c.a, c.b) >= c.r + delta * (1 - 1e-9)) continue
    const [onEdge] = segSegClosest(a, b, c.a, c.b)
    if (licensedHit(onEdge, c, lic, delta)) continue
    out.push(c)
  }
  return out
}

// ---------------------------------------------------------------------------
// Clearance grid
// ---------------------------------------------------------------------------

/** Cell size h = δ/2: fine enough that every legal corridor wider than
    2(δ + cellRadius) stays traversable, coarse enough to stay fast. A cell
    is blocked when its CENTER is within (r + δ + cellRadius) of a capsule,
    so any polyline through open cell centers clears every obstacle by ≥ δ —
    the guarantee is the grid's construction, not an aspiration. */
type Grid = {
  min: Vec3
  h: number
  nx: number
  ny: number
  nz: number
  blocked: Uint8Array
}

const cellRadius = (g: Grid): number => (g.h * Math.sqrt(3)) / 2

const cellIndex = (g: Grid, ix: number, iy: number, iz: number): number =>
  (iz * g.ny + iy) * g.nx + ix

const cellOf = (g: Grid, p: Vec3): [number, number, number] => [
  Math.min(g.nx - 1, Math.max(0, Math.round((p.x - g.min.x) / g.h))),
  Math.min(g.ny - 1, Math.max(0, Math.round((p.y - g.min.y) / g.h))),
  Math.min(g.nz - 1, Math.max(0, Math.round((p.z - g.min.z) / g.h))),
]

const centerOf = (g: Grid, ix: number, iy: number, iz: number): Vec3 =>
  v3(g.min.x + ix * g.h, g.min.y + iy * g.h, g.min.z + iz * g.h)

/** Room to detour around the outermost obstacle: its standoff plus slack. */
const GRID_MARGIN = 3

function buildGrid(caps: readonly Capsule[], extraPoints: readonly Vec3[], delta: number, h: number): Grid {
  let min = v3(Infinity, Infinity, Infinity)
  let max = v3(-Infinity, -Infinity, -Infinity)
  const eat = (p: Vec3): void => {
    min = v3(Math.min(min.x, p.x), Math.min(min.y, p.y), Math.min(min.z, p.z))
    max = v3(Math.max(max.x, p.x), Math.max(max.y, p.y), Math.max(max.z, p.z))
  }
  for (const c of caps) { eat(c.a); eat(c.b) }
  for (const p of extraPoints) eat(p)
  min = v3(min.x - GRID_MARGIN, min.y - GRID_MARGIN, min.z - GRID_MARGIN)
  max = v3(max.x + GRID_MARGIN, max.y + GRID_MARGIN, max.z + GRID_MARGIN)
  const nx = Math.max(2, Math.ceil((max.x - min.x) / h) + 1)
  const ny = Math.max(2, Math.ceil((max.y - min.y) / h) + 1)
  const nz = Math.max(2, Math.ceil((max.z - min.z) / h) + 1)
  const g: Grid = { min, h, nx, ny, nz, blocked: new Uint8Array(nx * ny * nz) }
  rasterize(g, caps, delta)
  return g
}

/** Mark blocked cells for `caps` (incremental: call again as wires land). */
function rasterize(g: Grid, caps: readonly Capsule[], delta: number): void {
  const pad = delta + cellRadius(g)
  for (const c of caps) {
    const reach = c.r + pad
    const lo = cellOf(g, v3(Math.min(c.a.x, c.b.x) - reach, Math.min(c.a.y, c.b.y) - reach, Math.min(c.a.z, c.b.z) - reach))
    const hi = cellOf(g, v3(Math.max(c.a.x, c.b.x) + reach, Math.max(c.a.y, c.b.y) + reach, Math.max(c.a.z, c.b.z) + reach))
    for (let iz = lo[2]; iz <= hi[2]; iz++) for (let iy = lo[1]; iy <= hi[1]; iy++) for (let ix = lo[0]; ix <= hi[0]; ix++) {
      if (g.blocked[cellIndex(g, ix, iy, iz)] === 1) continue
      if (segPointDist(centerOf(g, ix, iy, iz), c.a, c.b) < reach) g.blocked[cellIndex(g, ix, iy, iz)] = 1
    }
  }
}

/** Blocked cells inside a net's exemption balls whose every blocker is
    licensed there become traversable FOR THIS NET. */
function licensedOpenCells(
  g: Grid, lic: License, idx: CapsuleIndex, delta: number,
): Set<number> {
  const open = new Set<number>()
  const pad = delta + cellRadius(g)
  for (const b of lic.balls) {
    const r = 2.5 * delta
    const lo = cellOf(g, v3(b.e.x - r, b.e.y - r, b.e.z - r))
    const hi = cellOf(g, v3(b.e.x + r, b.e.y + r, b.e.z + r))
    for (let iz = lo[2]; iz <= hi[2]; iz++) for (let iy = lo[1]; iy <= hi[1]; iy++) for (let ix = lo[0]; ix <= hi[0]; ix++) {
      const ci = cellIndex(g, ix, iy, iz)
      if (g.blocked[ci] === 0 || open.has(ci)) continue
      const p = centerOf(g, ix, iy, iz)
      if (dist3(p, b.e) >= r) continue
      if (penetrations(p, idx, pad).every((c) => licensedHit(p, c, lic, delta))) open.add(ci)
    }
  }
  return open
}

/** The 26 lattice steps with their Euclidean lengths (unit h). */
const STEPS: readonly { dx: number; dy: number; dz: number; w: number }[] = (() => {
  const out: { dx: number; dy: number; dz: number; w: number }[] = []
  for (const dx of [-1, 0, 1]) for (const dy of [-1, 0, 1]) for (const dz of [-1, 0, 1]) {
    if (dx === 0 && dy === 0 && dz === 0) continue
    out.push({ dx, dy, dz, w: Math.hypot(dx, dy, dz) })
  }
  return out
})()

/** Binary min-heap over (score, insertion order) — deterministic. */
class Heap {
  private ks: number[] = []
  private vs: number[] = []
  private seq: number[] = []
  private n = 0
  private tick = 0
  push(key: number, value: number): void {
    let i = this.n++
    this.ks[i] = key; this.vs[i] = value; this.seq[i] = this.tick++
    while (i > 0) {
      const p = (i - 1) >> 1
      if (this.ks[p]! < this.ks[i]! || (this.ks[p]! === this.ks[i]! && this.seq[p]! < this.seq[i]!)) break
      this.swap(p, i); i = p
    }
  }
  pop(): number {
    const top = this.vs[0]!
    this.n--
    if (this.n > 0) {
      this.ks[0] = this.ks[this.n]!; this.vs[0] = this.vs[this.n]!; this.seq[0] = this.seq[this.n]!
      let i = 0
      for (;;) {
        const l = 2 * i + 1, r = l + 1
        let m = i
        if (l < this.n && (this.ks[l]! < this.ks[m]! || (this.ks[l]! === this.ks[m]! && this.seq[l]! < this.seq[m]!))) m = l
        if (r < this.n && (this.ks[r]! < this.ks[m]! || (this.ks[r]! === this.ks[m]! && this.seq[r]! < this.seq[m]!))) m = r
        if (m === i) break
        this.swap(m, i); i = m
      }
    }
    return top
  }
  get size(): number { return this.n }
  private swap(a: number, b: number): void {
    const k = this.ks[a]!; this.ks[a] = this.ks[b]!; this.ks[b] = k
    const vv = this.vs[a]!; this.vs[a] = this.vs[b]!; this.vs[b] = vv
    const s = this.seq[a]!; this.seq[a] = this.seq[b]!; this.seq[b] = s
  }
}

type Box = { lo: [number, number, number]; hi: [number, number, number] }

function boxAround(g: Grid, pts: readonly Vec3[], marginCells: number): Box {
  const lo: [number, number, number] = [g.nx - 1, g.ny - 1, g.nz - 1]
  const hi: [number, number, number] = [0, 0, 0]
  for (const p of pts) {
    const c = cellOf(g, p)
    for (let d = 0; d < 3; d++) {
      lo[d] = Math.min(lo[d]!, c[d]!)
      hi[d] = Math.max(hi[d]!, c[d]!)
    }
  }
  const dims = [g.nx, g.ny, g.nz]
  for (let d = 0; d < 3; d++) {
    lo[d] = Math.max(0, lo[d]! - marginCells)
    hi[d] = Math.min(dims[d]! - 1, hi[d]! + marginCells)
  }
  return { lo, hi }
}

/** Box-local dense state: local index = ((iz-lo)*bny + (iy-lo))*bnx + (ix-lo). */
type BoxState = {
  box: Box
  bnx: number
  bny: number
  bnz: number
}
const mkBoxState = (box: Box): BoxState => ({
  box,
  bnx: box.hi[0] - box.lo[0] + 1,
  bny: box.hi[1] - box.lo[1] + 1,
  bnz: box.hi[2] - box.lo[2] + 1,
})
const localIndex = (b: BoxState, ix: number, iy: number, iz: number): number =>
  ((iz - b.box.lo[2]) * b.bny + (iy - b.box.lo[1])) * b.bnx + (ix - b.box.lo[0])
const inBox = (b: Box, ix: number, iy: number, iz: number): boolean =>
  ix >= b.lo[0] && ix <= b.hi[0] && iy >= b.lo[1] && iy <= b.hi[1] && iz >= b.lo[2] && iz <= b.hi[2]

/** Nearest traversable cell to `p` (spiral over expanding cubes). */
function nearestOpen(g: Grid, open: (idx: number) => boolean, p: Vec3, maxShells: number): [number, number, number] | null {
  const [cx, cy, cz] = cellOf(g, p)
  for (let s = 0; s <= maxShells; s++) {
    for (let iz = Math.max(0, cz - s); iz <= Math.min(g.nz - 1, cz + s); iz++) {
      for (let iy = Math.max(0, cy - s); iy <= Math.min(g.ny - 1, cy + s); iy++) {
        for (let ix = Math.max(0, cx - s); ix <= Math.min(g.nx - 1, cx + s); ix++) {
          if (Math.max(Math.abs(ix - cx), Math.abs(iy - cy), Math.abs(iz - cz)) !== s) continue
          if (open(cellIndex(g, ix, iy, iz))) return [ix, iy, iz]
        }
      }
    }
  }
  return null
}

/** A* shortest clear path from `from` to `to` within `box`. Returns world
    waypoints (exact endpoints preserved) or null when no path exists. The
    start/goal cells must not only be open — the straight CONNECTING
    segment from the exact endpoint to the cell center must itself be
    clear, or the first/last hop grazes a blocker the grid never modeled. */
function shortestPath(
  g: Grid, open: (idx: number) => boolean, from: Vec3, to: Vec3, box: Box,
  connectable: (exact: Vec3, center: Vec3) => boolean,
): Vec3[] | null {
  const openConn = (exact: Vec3) => (idx: number): boolean => {
    if (!open(idx)) return false
    const ix = idx % g.nx
    const iy = ((idx - ix) / g.nx) % g.ny
    const iz = (idx - ix - iy * g.nx) / (g.nx * g.ny)
    return connectable(exact, centerOf(g, ix, iy, iz))
  }
  const start = nearestOpen(g, openConn(from), from, 3)
  const goal = nearestOpen(g, openConn(to), to, 3)
  if (start === null || goal === null) return null
  const bs = mkBoxState(box)
  const nCells = bs.bnx * bs.bny * bs.bnz
  const gScore = new Float64Array(nCells).fill(Infinity)
  const cameFrom = new Int32Array(nCells).fill(-1)
  const heap = new Heap()
  const startL = localIndex(bs, start[0], start[1], start[2])
  const goalL = localIndex(bs, goal[0], goal[1], goal[2])
  const goalC = centerOf(g, goal[0], goal[1], goal[2])
  gScore[startL] = 0
  heap.push(dist3(centerOf(g, start[0], start[1], start[2]), goalC), startL)
  const decodeL = (l: number): [number, number, number] => {
    const lx = l % bs.bnx
    const ly = ((l - lx) / bs.bnx) % bs.bny
    const lz = (l - lx - ly * bs.bnx) / (bs.bnx * bs.bny)
    return [lx + box.lo[0], ly + box.lo[1], lz + box.lo[2]]
  }
  while (heap.size > 0) {
    const cur = heap.pop()
    if (cur === goalL) {
      const cells: number[] = [cur]
      let walk = cur
      while (cameFrom[walk]! >= 0) {
        walk = cameFrom[walk]!
        cells.push(walk)
      }
      cells.reverse()
      const way = cells.map((l) => {
        const [ix, iy, iz] = decodeL(l)
        return centerOf(g, ix, iy, iz)
      })
      return [from, ...way, to]
    }
    const [ix, iy, iz] = decodeL(cur)
    const gCur = gScore[cur]!
    for (const st of STEPS) {
      const nx2 = ix + st.dx, ny2 = iy + st.dy, nz2 = iz + st.dz
      if (!inBox(box, nx2, ny2, nz2)) continue
      if (!open(cellIndex(g, nx2, ny2, nz2))) continue
      const nL = localIndex(bs, nx2, ny2, nz2)
      const tentative = gCur + st.w * g.h
      if (gScore[nL]! <= tentative) continue
      gScore[nL] = tentative
      cameFrom[nL] = cur
      heap.push(tentative + dist3(centerOf(g, nx2, ny2, nz2), goalC), nL)
    }
  }
  return null
}

/** Dijkstra distance field from `src` over `box` (box-local Float64Array;
    Infinity = unreachable). */
function distanceField(
  g: Grid, open: (idx: number) => boolean, src: Vec3, bs: BoxState,
): Float64Array | null {
  const start = nearestOpen(g, open, src, 3)
  if (start === null) return null
  const nCells = bs.bnx * bs.bny * bs.bnz
  const field = new Float64Array(nCells).fill(Infinity)
  const heap = new Heap()
  const sL = localIndex(bs, start[0], start[1], start[2])
  field[sL] = 0
  heap.push(0, sL)
  const decodeL = (l: number): [number, number, number] => {
    const lx = l % bs.bnx
    const ly = ((l - lx) / bs.bnx) % bs.bny
    const lz = (l - lx - ly * bs.bnx) / (bs.bnx * bs.bny)
    return [lx + bs.box.lo[0], ly + bs.box.lo[1], lz + bs.box.lo[2]]
  }
  const settled = new Uint8Array(nCells)
  while (heap.size > 0) {
    const cur = heap.pop()
    if (settled[cur] === 1) continue
    settled[cur] = 1
    const [ix, iy, iz] = decodeL(cur)
    const dCur = field[cur]!
    for (const st of STEPS) {
      const nx2 = ix + st.dx, ny2 = iy + st.dy, nz2 = iz + st.dz
      if (!inBox(bs.box, nx2, ny2, nz2)) continue
      if (!open(cellIndex(g, nx2, ny2, nz2))) continue
      const nL = localIndex(bs, nx2, ny2, nz2)
      const tentative = dCur + st.w * g.h
      if (field[nL]! <= tentative) continue
      field[nL] = tentative
      heap.push(tentative, nL)
    }
  }
  return field
}

// ---------------------------------------------------------------------------
// Verified length descent (unchanged laws: taut chords, rounded corners)
// ---------------------------------------------------------------------------

/** Subdivide a waypoint path to ~delta/2 sample spacing. */
function densifyWaypoints(way: readonly Vec3[], delta: number): Vec3[] {
  const out: Vec3[] = [way[0]!]
  for (let k = 1; k < way.length; k++) {
    const a = way[k - 1]!, b = way[k]!
    const pieces = Math.max(1, Math.ceil(dist3(a, b) / (delta / 2)))
    for (let t = 1; t <= pieces; t++) out.push(lerp3(a, b, t / pieces))
  }
  return out
}

/** Pull the path TAUT over verified-clear chords, re-densify, then ROUND
    corners with clearance-verified smoothing to a fixpoint — pure length
    descent inside the clear space; every accepted move re-verifies the same
    edge invariant the final check enforces. */
function beautify(pts: Vec3[], idx: CapsuleIndex, lic: License, delta: number): Vec3[] {
  if (pts.length < 4) return pts
  const last = pts.length - 1
  const taut: Vec3[] = [pts[0]!]
  let i = 0
  while (i < last) {
    let j = last
    while (j > i + 1 && edgeHits(pts[i]!, pts[j]!, idx, lic, delta).length !== 0) {
      j = i + Math.floor((j - i) / 2)
    }
    taut.push(pts[j]!)
    i = j
  }
  const dense = densifyWaypoints(taut, delta)
  for (let round = 0; round < 200; round++) {
    let moved = 0
    for (let k = 1; k < dense.length - 1; k++) {
      const mid = scale3(add3(dense[k - 1]!, dense[k + 1]!), 0.5)
      const cand = add3(dense[k]!, scale3(sub3(mid, dense[k]!), SMOOTH))
      if (edgeHits(dense[k - 1]!, cand, idx, lic, delta).length === 0
        && edgeHits(cand, dense[k + 1]!, idx, lic, delta).length === 0) {
        moved = Math.max(moved, dist3(cand, dense[k]!))
        dense[k] = cand
      }
    }
    if (moved < 1e-3 * delta) break
  }
  return dense
}

const chainOf = (pts: Vec3[], g: string): Capsule[] => pts.slice(1).map((b, i) => ({ a: pts[i]!, b, r: 0, g }))

// ---------------------------------------------------------------------------
// The router
// ---------------------------------------------------------------------------

/** Cells a wire-local box must extend beyond its endpoints so a detour
    around the largest obstacle standoff fits (GRID_MARGIN in cells). */
const boxMarginCells = (g: Grid): number => Math.ceil(GRID_MARGIN / g.h)

export function routeAll(nets: NetIn[], tree: Capsule[], delta: number): Map<WireId, Vec3[][]> {
  const idx = new CapsuleIndex(delta)
  for (const c of tree) idx.push(c)
  // Every wire's construction geometry — anchors AND its stubs — is an
  // obstacle from the START, so no earlier wire can invade where a later
  // wire must attach. Each carries its owner's group, keeping the owner's
  // own access licensed.
  for (const net of nets) {
    const own = `w:${net.id}`
    for (const a of net.anchors) idx.push({ a, b: a, r: 0, g: own })
    for (const [ai, fi] of net.stubs) {
      idx.push({ a: net.anchors[ai]!, b: net.fixedJunctions[fi]!, r: 0, g: own })
    }
  }
  const everyPoint = nets.flatMap((n) => [...n.anchors, ...n.fixedJunctions])
  const grid = buildGrid(idx.caps, everyPoint, delta, delta / 2)
  // Junction fields only pick a CELL, not a path — δ resolution suffices
  // and costs 8× less than the path grid.
  const coarse = buildGrid(idx.caps, everyPoint, delta, delta)

  const out = new Map<WireId, Vec3[][]>()
  for (const net of nets) {
    const own = `w:${net.id}`
    const fixedBase = net.anchors.length + net.freeJunctionCount
    const ballPts = [...net.anchors, ...net.fixedJunctions]
    const mkLic = (extra: readonly Vec3[]): License => ({
      own,
      balls: [...ballPts, ...extra].map((e) => ({ e, groups: groupsNearIdx(e, idx, delta) })),
    })
    let lic = mkLic([])
    let openOverride = licensedOpenCells(grid, lic, idx, delta)
    // Own routed edges block their cells for this wire's LATER edges except
    // near the shared meeting balls, so a wire cannot cross itself.
    const ownBlocked = new Set<number>()
    const open = (ci: number): boolean =>
      (grid.blocked[ci] === 0 || openOverride.has(ci)) && !ownBlocked.has(ci)

    // Free junction placement: obstacle-aware 1-median — argmin of summed
    // distance fields from the junction's network neighbors, refined by
    // deterministic sweeps (monotone in total routed length; capped, and a
    // cap leaves positions merely suboptimal, never invalid).
    const junctionPos: Vec3[] = new Array<Vec3>(net.freeJunctionCount)
    if (net.freeJunctionCount > 0) {
      const coarseOpen = (ci: number): boolean => coarse.blocked[ci] === 0
      const bs = mkBoxState(boxAround(coarse, [...net.anchors, ...net.fixedJunctions], boxMarginCells(coarse)))
      const posOfVertex = (vv: number): Vec3 | null => {
        if (vv < net.anchors.length) return net.anchors[vv]!
        if (vv >= fixedBase) return net.fixedJunctions[vv - fixedBase]!
        return junctionPos[vv - net.anchors.length] ?? null
      }
      const neighborsOf = (j: number): number[] => {
        const vertex = net.anchors.length + j
        const ns: number[] = []
        for (const [u, vv] of net.edges) {
          if (u === vertex) ns.push(vv)
          if (vv === vertex) ns.push(u)
        }
        return ns
      }
      // Fields from FIXED sources never change across sweeps; cache them by
      // source position so a sweep only pays for junction-source fields.
      const fieldCache = new Map<string, Float64Array | null>()
      const fieldFor = (p: Vec3): Float64Array | null => {
        const key = `${p.x},${p.y},${p.z}`
        const hit = fieldCache.get(key)
        if (hit !== undefined) return hit
        const f = distanceField(coarse, coarseOpen, p, bs)
        fieldCache.set(key, f)
        return f
      }
      for (let sweep = 0; sweep < 3; sweep++) {
        let movedCells = false
        for (let j = 0; j < net.freeJunctionCount; j++) {
          const fields: Float64Array[] = []
          for (const nb of neighborsOf(j)) {
            const p = posOfVertex(nb)
            if (p === null) continue
            const f = fieldFor(p)
            if (f !== null) fields.push(f)
          }
          if (fields.length === 0) continue
          let bestL = -1
          let bestSum = Infinity
          const nCells = bs.bnx * bs.bny * bs.bnz
          for (let l = 0; l < nCells; l++) {
            let sum = 0
            for (const f of fields) {
              sum += f[l]!
              if (sum === Infinity) break
            }
            if (sum < bestSum) {
              bestSum = sum
              bestL = l
            }
          }
          if (bestL < 0 || bestSum === Infinity) throw new Error(`route3: no reachable junction cell for ${net.id}`)
          const lx = bestL % bs.bnx
          const ly = ((bestL - lx) / bs.bnx) % bs.bny
          const lz = (bestL - lx - ly * bs.bnx) / (bs.bnx * bs.bny)
          const cand = centerOf(coarse, lx + bs.box.lo[0], ly + bs.box.lo[1], lz + bs.box.lo[2])
          if (junctionPos[j] === undefined || dist3(cand, junctionPos[j]!) > 1e-9) movedCells = true
          junctionPos[j] = cand
        }
        if (!movedCells) break
      }
      lic = mkLic(junctionPos)
      openOverride = licensedOpenCells(grid, lic, idx, delta)
    }

    const posOf = (vv: number): Vec3 => {
      if (vv < net.anchors.length) return net.anchors[vv]!
      if (vv >= fixedBase) return net.fixedJunctions[vv - fixedBase]!
      return junctionPos[vv - net.anchors.length]!
    }
    const stubEdges = new Set(net.stubs.map(([ai, fi]) => `${ai}:${fixedBase + fi}`))
    const isStubEdge = (u: number, w: number): boolean =>
      stubEdges.has(`${u}:${w}`) || stubEdges.has(`${w}:${u}`)

    const curves: Vec3[][] = []
    const ownCaps: Capsule[] = []
    net.edges.forEach(([u, w], i) => {
      const p = posOf(u), q = posOf(w)
      let pts: Vec3[]
      if (dist3(p, q) < 1e-9) {
        pts = [p, q]
      } else if (isStubEdge(u, w)) {
        // Construction stubs are drawn AS CONSTRUCTED — a straight segment
        // whose legality the sizing rules guarantee continuously (adjacent
        // stubs are ≥ δ apart). The grid's conservative cell margin would
        // wrongly seal such legal-but-tight corridors, so stubs never
        // consult it; they are still verified like everything else below.
        pts = densifyWaypoints([p, q], delta)
      } else {
        const box = boxAround(grid, [p, q], boxMarginCells(grid))
        const connectable = (exact: Vec3, center: Vec3): boolean =>
          edgeHits(exact, center, idx, lic, delta).length === 0
        const way = shortestPath(grid, open, p, q, box, connectable)
          ?? shortestPath(grid, open, p, q, { lo: [0, 0, 0], hi: [grid.nx - 1, grid.ny - 1, grid.nz - 1] }, connectable)
        if (way === null) throw new Error(`route3: no clear path for ${net.id}[${i}]`)
        pts = beautify(densifyWaypoints(way, delta), idx, lic, delta)
      }
      // The guarantee is VERIFIED, never assumed: every edge of the final
      // curve must clear every obstacle outside the licensed meeting zones.
      for (let k = 1; k < pts.length; k++) {
        const bad = edgeHits(pts[k - 1]!, pts[k]!, idx, lic, delta)
        if (bad.length > 0) throw new Error(`route3: clearance violation in ${net.id}[${i}] near sample ${k}`)
      }
      curves.push(pts)
      const caps = chainOf(pts, own)
      for (const c of caps) idx.push(c)
      ownCaps.push(...caps)
      // Block this edge's cells for the wire's remaining edges (except near
      // meeting balls, where edges legitimately converge).
      const pad = delta + cellRadius(grid)
      for (const c of caps) {
        const lo = cellOf(grid, v3(Math.min(c.a.x, c.b.x) - pad, Math.min(c.a.y, c.b.y) - pad, Math.min(c.a.z, c.b.z) - pad))
        const hi = cellOf(grid, v3(Math.max(c.a.x, c.b.x) + pad, Math.max(c.a.y, c.b.y) + pad, Math.max(c.a.z, c.b.z) + pad))
        for (let iz = lo[2]; iz <= hi[2]; iz++) for (let iy = lo[1]; iy <= hi[1]; iy++) for (let ix = lo[0]; ix <= hi[0]; ix++) {
          const center = centerOf(grid, ix, iy, iz)
          if (segPointDist(center, c.a, c.b) >= pad) continue
          if (lic.balls.some((b) => dist3(center, b.e) < 2.5 * delta)) continue
          ownBlocked.add(cellIndex(grid, ix, iy, iz))
        }
      }
    })
    out.set(net.id, curves)
    rasterize(grid, ownCaps, delta)
  }
  return out
}
