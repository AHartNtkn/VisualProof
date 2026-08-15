import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { relSig, IOTA } from '../../src/kernel/diagram/sig'
import { scene3, type Entity } from '../../src/view3d/scene'
import { CLEARANCE } from '../../src/view3d/layout'
import { dist3, segPointDist, type Vec3 } from '../../src/view3d/vec3'

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
  it('emits one branch per region, a bead per cut, rings and a ref label', () => {
    const { d, c1, P, Q, R } = fixture()
    const s = scene3(d)
    const byKind = (k: Entity['kind']) => s.entities.filter((e) => e.kind === k)
    expect(byKind('branch').map((e) => e.key).sort()).toEqual(['b:r0', `b:${c1}`].sort())
    expect(byKind('bead').map((e) => e.key)).toEqual([`d:${c1}`])
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
