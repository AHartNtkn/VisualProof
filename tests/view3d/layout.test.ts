import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { relSig, IOTA } from '../../src/kernel/diagram/sig'
import type { Diagram, RegionId } from '../../src/kernel/diagram/diagram'
import { diagramSpec } from '../../src/view3d/spec'
import { CLEARANCE, layoutTree, type TreeLayout } from '../../src/view3d/layout'
import { add3, dist3, dot3, lerp3, scale3, sub3, type Vec3 } from '../../src/view3d/vec3'

const layoutOf = (d: Diagram): TreeLayout => layoutTree(diagramSpec(d))

/** Sampled content geometry per region: its own line from contentStart to tip
    (the stem is boundary-crossing by design and exempt), plus its rings. */
function contentSamples(tl: TreeLayout, spec: ReturnType<typeof diagramSpec>): Map<RegionId, Vec3[]> {
  const out = new Map<RegionId, Vec3[]>()
  for (const [rid, pr] of tl.regions) {
    const pts: Vec3[] = []
    const start = add3(pr.base, scale3(pr.dir, pr.contentStart))
    for (let i = 0; i <= 40; i++) pts.push(lerp3(start, pr.tip, i / 40))
    for (const item of spec.regions.get(rid)!.items) {
      if (item.kind !== 'node') continue
      const ring = tl.rings.get(item.id)
      if (ring !== undefined) for (const a of ring.anchors.values()) pts.push(a)
    }
    out.set(rid, pts)
  }
  return out
}

const isAncestor = (spec: ReturnType<typeof diagramSpec>, a: RegionId, b: RegionId): boolean => {
  for (let cur: RegionId | null = b; cur !== null; cur = spec.regions.get(cur)!.parent) if (cur === a) return true
  return false
}

function busyFixture() {
  const b = new DiagramBuilder()
  const c1 = b.cut(b.root)
  const c2 = b.cut(b.root)
  const c3 = b.cut(c1)
  const P = b.atom(b.root, relSig([IOTA]))
  const Q = b.atom(c1, relSig([IOTA, IOTA]))
  const R = b.atom(c2, relSig([IOTA]))
  const S = b.atom(c3, relSig([IOTA]))
  b.wire([
    { node: P, port: { kind: 'arg', index: 0 } },
    { node: Q, port: { kind: 'arg', index: 0 } },
  ])
  b.wire([
    { node: Q, port: { kind: 'arg', index: 1 } },
    { node: S, port: { kind: 'arg', index: 0 } },
  ])
  return { d: b.build(), c1, c2, c3, P, Q, R, S }
}

describe('layoutTree', () => {
  it('lone-chain cuts continue collinearly', () => {
    const b = new DiagramBuilder()
    const c1 = b.cut(b.root)
    const c2 = b.cut(c1)
    b.point(c2)
    const tl = layoutOf(b.build())
    const r0 = tl.regions.get('r0')!, p1 = tl.regions.get(c1)!, p2 = tl.regions.get(c2)!
    expect(dot3(r0.dir, p1.dir)).toBeCloseTo(1, 9)
    expect(dot3(p1.dir, p2.dir)).toBeCloseTo(1, 9)
  })
  it('a region holding only cuts still shows a visible line (the sheet must never vanish)', () => {
    // A childed region's length comes from its nodes; with zero nodes the
    // sheet's line collapsed to a point — every non-empty diagram lost its
    // sheet branch (USER report 2026-08-16), which made the polarity
    // colors read as inverted.
    const b = new DiagramBuilder()
    const c1 = b.cut(b.root)
    const c2 = b.cut(c1)
    b.point(c2)
    const tl = layoutOf(b.build())
    for (const pr of tl.regions.values()) {
      expect(dist3(pr.base, pr.tip)).toBeGreaterThanOrEqual(0.45)
    }
  })
  it('sibling cuts leave at distinct azimuths and stay ≥ δ apart (sampled)', () => {
    const { d } = busyFixture()
    const spec = diagramSpec(d)
    const tl = layoutTree(spec)
    const samples = contentSamples(tl, spec)
    const beadChain = (rid: RegionId): Vec3[] => {
      const out: Vec3[] = []
      for (let cur: RegionId | null = rid; cur !== null; cur = spec.regions.get(cur)!.parent) {
        const pr = tl.regions.get(cur)!
        out.push(pr.base)
      }
      return out
    }
    for (const [ra, pa] of samples) for (const [rb, pb] of samples) {
      if (ra >= rb) continue
      const related = isAncestor(spec, ra, rb) || isAncestor(spec, rb, ra)
      const exempt = related ? [...beadChain(ra), ...beadChain(rb)] : []
      for (const x of pa) for (const y of pb) {
        if (exempt.some((e) => dist3(x, e) < 3 * CLEARANCE || dist3(y, e) < 3 * CLEARANCE)) continue
        expect(dist3(x, y)).toBeGreaterThanOrEqual(CLEARANCE * 0.95)
      }
    }
  })
  it('segment length grows with node content (port count)', () => {
    const mk = (arity: number): number => {
      const b = new DiagramBuilder()
      b.atom(b.root, relSig(Array.from({ length: arity }, () => IOTA)))
      const tl = layoutOf(b.build())
      const r = tl.regions.get('r0')!
      return dist3(add3(r.base, scale3(r.dir, r.contentStart)), r.tip)
    }
    expect(mk(6)).toBeGreaterThan(mk(1))
  })
  it('a wire escaping a cut widens that cut’s berth (longer stem)', () => {
    // c1 needs a sibling: a lone child continues collinearly with a fixed
    // stem, so the escape-driven clearance only shows on a fanned branch.
    const mk = (cross: boolean): number => {
      const b = new DiagramBuilder()
      const c1 = b.cut(b.root)
      const c2 = b.cut(b.root)
      b.point(c2)
      const P = b.atom(b.root, relSig([IOTA]))
      const Q = b.atom(c1, relSig([IOTA]))
      if (cross) {
        const w = b.wire([
          { node: P, port: { kind: 'arg', index: 0 } },
          { node: Q, port: { kind: 'arg', index: 0 } },
        ])
        b.pin(w, b.root)
        b.pin(w, c1)
      }
      const tl = layoutOf(b.build())
      return tl.regions.get(c1)!.contentStart
    }
    expect(mk(true)).toBeGreaterThan(mk(false))
  })
  it('all sibling branches fan from their parent segment tip', () => {
    const { d } = busyFixture()
    const spec = diagramSpec(d)
    const tl = layoutTree(spec)
    for (const [rid, pr] of tl.regions) {
      for (const child of tl.regions.values()) {
        if (spec.regions.get(child.region)!.parent !== rid) continue
        expect(dist3(child.base, pr.tip)).toBeLessThan(1e-9)
      }
    }
  })
  it('a parented segment ends at its fan point — no bare spike past the last node', () => {
    const { d, c1 } = busyFixture()
    const spec = diagramSpec(d)
    const tl = layoutTree(spec)
    const pr = tl.regions.get(c1)!
    let nearest = Infinity
    for (const item of spec.regions.get(c1)!.items) {
      if (item.kind !== 'node') continue
      const pos = tl.rings.get(item.id)?.center ?? tl.identityAnchor.get(item.id)!
      nearest = Math.min(nearest, dist3(pos, pr.tip))
    }
    // The tip sits half a spacing past the last node — never a tip pad plus
    // branch-point spacings beyond it.
    expect(nearest).toBeLessThanOrEqual(0.7)
  })
  it('branch lead-ins stay short — never scaled by subtree size', () => {
    const b = new DiagramBuilder()
    const c1 = b.cut(b.root)
    const c2 = b.cut(b.root)
    const c3 = b.cut(c1)
    const c4 = b.cut(c1)
    b.atom(c3, relSig([IOTA, IOTA, IOTA]))
    b.atom(c4, relSig([IOTA, IOTA, IOTA]))
    b.atom(c2, relSig([IOTA]))
    const tl = layoutOf(b.build())
    for (const pr of tl.regions.values()) {
      expect(pr.contentStart).toBeLessThanOrEqual(2)
    }
  })
  it('ring anchors sit on the rim, in the plane perpendicular to the branch', () => {
    const { d, Q } = busyFixture()
    const tl = layoutOf(d)
    const ring = tl.rings.get(Q)!
    expect(ring.anchors.size).toBe(3) // hd, a:0, a:1
    for (const a of ring.anchors.values()) {
      expect(dist3(a, ring.center)).toBeCloseTo(ring.radius, 9)
      expect(Math.abs(dot3(sub3(a, ring.center), ring.axis))).toBeLessThan(1e-9)
    }
  })
  it('every subtree lies inside its declared sphere; children nest in parents', () => {
    const { d } = busyFixture()
    const spec = diagramSpec(d)
    const tl = layoutTree(spec)
    const samples = contentSamples(tl, spec)
    for (const [rid, pts] of samples) {
      for (let cur: RegionId | null = rid; cur !== null; cur = spec.regions.get(cur)!.parent) {
        const s = tl.spheres.get(cur)!
        for (const p of pts) expect(dist3(p, s.center)).toBeLessThanOrEqual(s.r + 1e-6)
      }
    }
  })
  it('is deterministic', () => {
    const { d } = busyFixture()
    expect(JSON.stringify([...layoutOf(d).regions])).toBe(JSON.stringify([...layoutOf(d).regions]))
  })
})
