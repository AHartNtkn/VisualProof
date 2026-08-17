import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { relSig, IOTA } from '../../src/kernel/diagram/sig'
import { scene3, type Entity } from '../../src/view3d/scene'
import { CLEARANCE, layoutTree } from '../../src/view3d/layout'
import { diagramSpec } from '../../src/view3d/spec'
import { add3, dist3, dot3, scale3, segPointDist, sub3, type Vec3 } from '../../src/view3d/vec3'

function fixture() {
  const b = new DiagramBuilder()
  const c1 = b.cut(b.root)
  const P = b.atom(b.root, relSig([IOTA]))
  const Q = b.atom(c1, relSig([IOTA]))
  const R = b.ref(c1, 'Def', relSig([IOTA]))
  const x = b.wire([
    { node: P, port: { kind: 'arg', index: 0 } },
    { node: Q, port: { kind: 'arg', index: 0 } },
    { node: R, port: { kind: 'arg', index: 0 } },
  ])
  return { d: b.build(), c1, P, Q, R, x }
}

describe('scene3', () => {
  it('emits one polarity-colored branch per region, rings and a ref label', () => {
    const { d, c1, P, Q, R } = fixture()
    const s = scene3(d)
    const byKind = (k: Entity['kind']) => s.entities.filter((e) => e.kind === k)
    expect(byKind('branch').map((e) => e.key).sort()).toEqual(['b:r0', `b:${c1}`].sort())
    // Polarity replaces marker dots (USER ruling 2026-08-16): the sheet's
    // line is even, the cut's line odd — the crossing is a color change.
    const branchOf = (key: string) => byKind('branch').find((e) => e.key === key) as Extract<Entity, { kind: 'branch' }>
    expect(branchOf('b:r0').polarity).toBe(0)
    expect(branchOf(`b:${c1}`).polarity).toBe(1)
    expect(byKind('ring').map((e) => e.key).sort()).toEqual([`r:${P}`, `r:${Q}`, `r:${R}`].sort())
    const labels = byKind('label')
    expect(labels.length).toBe(1)
    expect((labels[0] as Extract<Entity, { kind: 'label' }>).text).toBe('Def')
  })
  it('every wire is drawn as a connected network covering its terminals', () => {
    const { d, x } = fixture()
    const s = scene3(d)
    const strands = s.entities.filter((e): e is Extract<Entity, { kind: 'strand' }> => e.kind === 'strand')
    const xStrands = strands.filter((e) => e.wire === x)
    // A connected network over k terminals needs ≥ k-1 edges; topology is
    // the solver's call (an obtuse triangle legitimately degenerates to a
    // 2-edge path through its wide vertex).
    expect(xStrands.length).toBeGreaterThanOrEqual(2)
    // Full terminal coverage: the strand endpoints must span ≥ 3 pairwise
    // distinct points (path: P,Q,R; Y: P,Q,R,junction).
    const ends = xStrands.flatMap((e) => [e.pts[0]!, e.pts[e.pts.length - 1]!])
    const distinct: Vec3[] = []
    for (const p of ends) if (!distinct.some((q) => dist3(p, q) < 1e-6)) distinct.push(p)
    expect(distinct.length).toBeGreaterThanOrEqual(3)
    // every strand key well-formed and unique
    const keys = strands.map((e) => e.key)
    expect(new Set(keys).size).toBe(keys.length)
  })
  it('strands keep δ clearance from branches and each other outside anchor balls', () => {
    const { d } = fixture()
    const s = scene3(d)
    const branches = s.entities.filter((e): e is Extract<Entity, { kind: 'branch' }> => e.kind === 'branch')
    const strands = s.entities.filter((e): e is Extract<Entity, { kind: 'strand' }> => e.kind === 'strand')
    // Exemption is per-wire (I7): derive each wire's OWN anchor set from its
    // OWN strands only — a point on wire A is never exempted by wire B's
    // endpoints.
    const anchorsByWire = new Map<string, Vec3[]>()
    for (const e of strands) {
      const list = anchorsByWire.get(e.wire) ?? []
      list.push(e.pts[0]!, e.pts[e.pts.length - 1]!)
      anchorsByWire.set(e.wire, list)
    }
    const nearAnchor = (wire: string, p: Vec3): boolean =>
      (anchorsByWire.get(wire) ?? []).some((a) => dist3(p, a) < 2.5 * CLEARANCE)
    for (const st of strands) {
      for (const p of st.pts) {
        if (nearAnchor(st.wire, p)) continue
        for (const br of branches) {
          expect(segPointDist(p, br.pts[0]!, br.pts[br.pts.length - 1]!)).toBeGreaterThanOrEqual(CLEARANCE * 0.95)
        }
      }
    }
    for (let i = 0; i < strands.length; i++) for (let j = i + 1; j < strands.length; j++) {
      for (const p of strands[i]!.pts) {
        if (nearAnchor(strands[i]!.wire, p)) continue
        for (let k = 1; k < strands[j]!.pts.length; k++) {
          if (nearAnchor(strands[j]!.wire, strands[j]!.pts[k]!)) continue
          expect(segPointDist(p, strands[j]!.pts[k - 1]!, strands[j]!.pts[k]!)).toBeGreaterThanOrEqual(CLEARANCE * 0.95)
        }
      }
    }
  })
  it('bounds contain every point', () => {
    const { d } = fixture()
    const s = scene3(d)
    for (const e of s.entities) {
      const pts: Vec3[] = 'pts' in e ? e.pts : [e.pos]
      for (const p of pts) expect(dist3(p, s.center)).toBeLessThanOrEqual(s.radius + 1e-9)
    }
    expect(s.radius).toBeGreaterThan(0)
    expect(Number.isFinite(s.center.x + s.center.y + s.center.z)).toBe(true)
  })
  it('is deterministic', () => {
    const { d } = fixture()
    expect(scene3(d)).toEqual(scene3(d))
  })
  it('every terminal anchor is a LEAF: exactly one strand end touches it', () => {
    // USER law 2026-08-15: a wire connects at the END of a branch. When the
    // minimal network degenerates to a path through a terminal, a standoff
    // junction takes the pass-through and the terminal hangs off it — so no
    // anchor ever has two strand ends (in-and-out, the "sharp pin").
    const { d, x } = fixture()
    const s = scene3(d)
    const tl = layoutTree(diagramSpec(d))
    const spec = diagramSpec(d)
    const wire = spec.wires.find((w) => w.id === x)!
    const strandEnds = s.entities
      .filter((e): e is Extract<Entity, { kind: 'strand' }> => e.kind === 'strand' && e.wire === x)
      .flatMap((e) => [e.pts[0]!, e.pts[e.pts.length - 1]!])
    for (const t of wire.terminals) {
      const anchor = tl.anchorOf(t)
      const touching = strandEnds.filter((p) => dist3(p, anchor) < 1e-6).length
      expect(touching).toBe(1)
    }
  })
  it('no strand crosses a ring disc interior', () => {
    // USER law 2026-08-15: wires connect to ring EXTERIORS only — the disc
    // interior is solid. Check every strand edge against every ring plane:
    // a sign change within the rim radius is a threading violation.
    const { d } = fixture()
    const s = scene3(d)
    const tl = layoutTree(diagramSpec(d))
    const strands = s.entities.filter((e): e is Extract<Entity, { kind: 'strand' }> => e.kind === 'strand')
    for (const ring of tl.rings.values()) {
      for (const st of strands) {
        for (let i = 1; i < st.pts.length; i++) {
          const da = dot3(sub3(st.pts[i - 1]!, ring.center), ring.axis)
          const db = dot3(sub3(st.pts[i]!, ring.center), ring.axis)
          if (da === 0 && db === 0) continue // in-plane approach along the rim, never a crossing
          if ((da > 0 && db > 0) || (da < 0 && db < 0)) continue
          const t = Math.abs(da) / (Math.abs(da) + Math.abs(db))
          const hit = add3(st.pts[i - 1]!, scale3(sub3(st.pts[i]!, st.pts[i - 1]!), t))
          expect(dist3(hit, ring.center)).toBeGreaterThanOrEqual(ring.radius * 0.999)
        }
      }
    }
  })
  it('a wire between nodes on the SAME branch arches off the line, touching it only at its ends', () => {
    // USER law 2026-08-15: a wire is NEVER parallel-and-overlapping with a
    // branch. Two identity nodes on the trunk joined by a wire must produce
    // strands that leave the line immediately: every sample farther than δ
    // from both of its strand's endpoints stays ≥ δ·0.95 off the branch.
    const b = new DiagramBuilder()
    const i1 = b.identity(b.root, IOTA, 1)
    const i2 = b.identity(b.root, IOTA, 1)
    b.wire([
      { node: i1, port: { kind: 'identity', index: 0 } },
      { node: i2, port: { kind: 'identity', index: 0 } },
    ])
    const d = b.build()
    const s = scene3(d)
    const tl = layoutTree(diagramSpec(d))
    const trunk = tl.regions.get('r0')!
    const strands = s.entities.filter((e): e is Extract<Entity, { kind: 'strand' }> => e.kind === 'strand')
    expect(strands.length).toBeGreaterThan(0)
    let arched = false
    for (const st of strands) {
      const first = st.pts[0]!, last = st.pts[st.pts.length - 1]!
      for (const p of st.pts) {
        const offLine = segPointDist(p, trunk.base, trunk.tip)
        if (offLine >= CLEARANCE * 0.95) arched = true
        if (dist3(p, first) <= CLEARANCE || dist3(p, last) <= CLEARANCE) continue
        expect(offLine).toBeGreaterThanOrEqual(CLEARANCE * 0.95)
      }
    }
    expect(arched).toBe(true)
  })
  it('identity nodes get pip entities carrying their owner wire', () => {
    // USER law 2026-08-15: identity nodes draw small pips over the branch
    // lines so they are visible. Owner wire = the first wire bound there
    // (the 2D bodyStroke rule), for hue-matched stroking.
    const b = new DiagramBuilder()
    const i1 = b.identity(b.root, IOTA, 1)
    const i2 = b.identity(b.root, IOTA, 1)
    const w = b.wire([
      { node: i1, port: { kind: 'identity', index: 0 } },
      { node: i2, port: { kind: 'identity', index: 0 } },
    ])
    const d = b.build()
    const s = scene3(d)
    const tl = layoutTree(diagramSpec(d))
    const pips = s.entities.filter((e): e is Extract<Entity, { kind: 'pip' }> => e.kind === 'pip')
    expect(pips.map((p) => p.key).sort()).toEqual([`p:${i1}`, `p:${i2}`].sort())
    for (const pip of pips) {
      expect(dist3(pip.pos, tl.identityAnchor.get(pip.node)!)).toBeLessThan(1e-9)
      expect(pip.ownerWire).toBe(w)
    }
  })
  it('ring connections depart radially OUTWARD — never from the branch side', () => {
    // USER law 2026-08-15: the side of an application circle facing its
    // branch is its interior; wires never connect there. Every strand end
    // sitting on a ring rim must leave along the outward normal (a straight
    // radial stub), so the visible connection always comes from outside.
    const { d } = fixture()
    const s = scene3(d)
    const tl = layoutTree(diagramSpec(d))
    const strands = s.entities.filter((e): e is Extract<Entity, { kind: 'strand' }> => e.kind === 'strand')
    let checked = 0
    for (const ring of tl.rings.values()) {
      for (const anchor of ring.anchors.values()) {
        for (const st of strands) {
          const ends: [Vec3, Vec3][] = [
            [st.pts[0]!, st.pts[1]!],
            [st.pts[st.pts.length - 1]!, st.pts[st.pts.length - 2]!],
          ]
          for (const [end, next] of ends) {
            if (dist3(end, anchor) > 1e-6) continue
            checked++
            const outward = scale3(sub3(anchor, ring.center), 1 / ring.radius)
            const dep = sub3(next, end)
            const depLen = Math.hypot(dep.x, dep.y, dep.z)
            expect(dot3(dep, outward) / depLen).toBeGreaterThanOrEqual(0.9)
          }
        }
      }
    }
    expect(checked).toBeGreaterThan(0)
  })
  it('rings carry their head wire for order-hue stroking; refs carry null', () => {
    const { d, P, R } = fixture()
    const spec = diagramSpec(d)
    const s = scene3(d)
    const ringOf = (n: string) => s.entities.find(
      (e): e is Extract<Entity, { kind: 'ring' }> => e.kind === 'ring' && e.node === n,
    )!
    const headWire = spec.wires.find((w) => w.terminals.some((t) => t.node === P && t.portKey === 'hd'))!
    expect(ringOf(P).headWire).toBe(headWire.id)
    expect(ringOf(R).headWire).toBeNull()
  })
  it('a 0-ary ref renders as a plain ring plus label, no anchors, no throw', () => {
    const b = new DiagramBuilder()
    const R = b.ref(b.root, 'Prop', relSig([]))
    const d = b.build()
    expect(() => scene3(d)).not.toThrow()
    const s = scene3(d)
    const ring = s.entities.find(
      (e): e is Extract<Entity, { kind: 'ring' }> => e.kind === 'ring' && e.node === R,
    )
    expect(ring).toBeDefined()
    expect(ring!.pts.length).toBeGreaterThan(0)
    const label = s.entities.find(
      (e): e is Extract<Entity, { kind: 'label' }> => e.kind === 'label' && e.node === R,
    )
    expect(label).toBeDefined()
    expect(label!.text).toBe('Prop')
  })
})
