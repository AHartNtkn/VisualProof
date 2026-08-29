import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { relSig, IOTA } from '../../src/kernel/diagram/sig'
import { diagramSpec } from '../../src/view3d/spec'
import { scene3, type Entity } from '../../src/view3d/scene'
import { expandHover, focusPoint } from '../../src/view3d/pick'
import { dist3 } from '../../src/view3d/vec3'

function fixture() {
  const b = new DiagramBuilder()
  const c1 = b.cut(b.root)
  const c2 = b.cut(c1)
  const P = b.atom(b.root, relSig([IOTA]))
  const R = b.ref(c1, 'Def', relSig([IOTA]))
  const wPR = b.wire([
    { node: P, port: { kind: 'arg', index: 0 } },
    { node: R, port: { kind: 'arg', index: 0 } },
  ])
  // A second, unrelated wire touching neither P nor R — exercises that
  // node-hover only picks up strands incident at THAT node, not every wire.
  const S = b.atom(c2, relSig([IOTA]))
  const T = b.atom(c2, relSig([IOTA]))
  const wST = b.wire([
    { node: S, port: { kind: 'arg', index: 0 } },
    { node: T, port: { kind: 'arg', index: 0 } },
  ])
  const d = b.build()
  return { d, spec: diagramSpec(d), scene: scene3(d), c1, c2, P, R, S, T, wPR, wST }
}

describe('expandHover', () => {
  it('a strand expands to every strand of its wire', () => {
    const { spec, scene } = fixture()
    const strand = scene.entities.find((e) => e.kind === 'strand')!
    const wid = (strand as Extract<typeof strand, { kind: 'strand' }>).wire
    const got = expandHover(strand.key, spec, scene.entities)
    const all = scene.entities.filter((e) => e.kind === 'strand' && e.wire === wid).map((e) => e.key)
    expect([...got].sort()).toEqual(all.sort())
  })
  it('a branch expands to its whole subtree of branches', () => {
    const { spec, scene, c1, c2 } = fixture()
    const c1Branch = scene.entities.find((e) => e.kind === 'branch' && e.region === c1)!
    const c2Branch = scene.entities.find((e) => e.kind === 'branch' && e.region === c2)!
    const rootBranch = scene.entities.find((e) => e.kind === 'branch' && e.region === 'r0')!
    const got = expandHover(c1Branch.key, spec, scene.entities)
    expect(got.has(c1Branch.key)).toBe(true)
    expect(got.has(c2Branch.key)).toBe(true)
    expect(got.has(rootBranch.key)).toBe(false)
  })
  it('a ring expands to ring + its label + incident wire anchors (spec: hovering a node highlights its ring plus incident wire anchors)', () => {
    const { spec, scene, R, wPR, wST } = fixture()
    const ring = scene.entities.find((e) => e.kind === 'ring' && e.node === R)!
    const label = scene.entities.find((e) => e.kind === 'label' && e.node === R)!
    const got = expandHover(ring.key, spec, scene.entities)
    expect(got.has(ring.key)).toBe(true)
    expect(got.has(label.key)).toBe(true)
    const strandsOf = (wid: string) => scene.entities.filter((e) => e.kind === 'strand' && e.wire === wid).map((e) => e.key)
    const ownStrands = strandsOf(wPR)
    expect(ownStrands.length).toBeGreaterThan(0)
    for (const k of ownStrands) expect(got.has(k)).toBe(true)
    // The unrelated wire (S-T, touching neither P nor R) must NOT light up.
    for (const k of strandsOf(wST)) expect(got.has(k)).toBe(false)
  })

  it('uses typed entity identity when drawing keys do not encode semantic ids', () => {
    const { spec, scene, c1, c2, R, wPR, wST } = fixture()
    const entities = scene.entities.map((entity, index) => ({ ...entity, key: `opaque-${index}` })) as Entity[]

    const branch = entities.find((e) => e.kind === 'branch' && e.region === c1)!
    const child = entities.find((e) => e.kind === 'branch' && e.region === c2)!
    const ring = entities.find((e) => e.kind === 'ring' && e.node === R)!
    const label = entities.find((e) => e.kind === 'label' && e.node === R)!
    const strand = entities.find((e) => e.kind === 'strand' && e.wire === wPR)!
    const pip = entities.find((e): e is Extract<Entity, { kind: 'pip' }> => e.kind === 'pip')!
    const ownStrands = entities.filter((e) => e.kind === 'strand' && e.wire === wPR)
    const unrelatedStrands = entities.filter((e) => e.kind === 'strand' && e.wire === wST)

    expect(expandHover(branch.key, spec, entities)).toEqual(new Set([branch.key, child.key]))

    const ringHover = expandHover(ring.key, spec, entities)
    expect(ringHover.has(label.key)).toBe(true)
    for (const entity of ownStrands) expect(ringHover.has(entity.key)).toBe(true)
    for (const entity of unrelatedStrands) expect(ringHover.has(entity.key)).toBe(false)

    expect(expandHover(strand.key, spec, entities)).toEqual(new Set(ownStrands.map((entity) => entity.key)))

    const pipIncidentWires = new Set(
      spec.wires.filter((wire) => wire.terminals.some((terminal) => terminal.node === pip.node)).map((wire) => wire.id),
    )
    const pipHover = expandHover(pip.key, spec, entities)
    expect(pipHover).toEqual(new Set([
      pip.key,
      ...entities.filter((e) => e.kind === 'strand' && pipIncidentWires.has(e.wire)).map((e) => e.key),
    ]))
  })

  it('preserves an unknown drawing key as the sole hover output', () => {
    const { spec, scene } = fixture()
    expect(expandHover('opaque-missing', spec, scene.entities)).toEqual(new Set(['opaque-missing']))
  })
})

describe('focusPoint', () => {
  it('a ring focuses its own center; a pip focuses its position', () => {
    const { scene } = fixture()
    const ring = scene.entities.find((e): e is Extract<Entity, { kind: 'ring' }> => e.kind === 'ring')!
    const p = focusPoint(ring.key, scene.entities)!
    // bbox center of the rim = the ring center
    let cx = 0, cy = 0, cz = 0
    const rim = ring.pts.slice(0, -1)
    for (const q of rim) { cx += q.x; cy += q.y; cz += q.z }
    const center = { x: cx / rim.length, y: cy / rim.length, z: cz / rim.length }
    expect(dist3(p, center)).toBeLessThan(0.05)
    const pip = scene.entities.find((e): e is Extract<Entity, { kind: 'pip' }> => e.kind === 'pip')!
    expect(dist3(focusPoint(pip.key, scene.entities)!, pip.pos)).toBeLessThan(1e-9)
  })
  it('a strand focuses its whole WIRE (bbox center of all its strands)', () => {
    const { scene, wPR } = fixture()
    const strands = scene.entities.filter(
      (e): e is Extract<Entity, { kind: 'strand' }> => e.kind === 'strand' && e.wire === wPR,
    )
    const p = focusPoint(strands[0]!.key, scene.entities)!
    let lo = { x: Infinity, y: Infinity, z: Infinity }, hi = { x: -Infinity, y: -Infinity, z: -Infinity }
    for (const st of strands) for (const q of st.pts) {
      lo = { x: Math.min(lo.x, q.x), y: Math.min(lo.y, q.y), z: Math.min(lo.z, q.z) }
      hi = { x: Math.max(hi.x, q.x), y: Math.max(hi.y, q.y), z: Math.max(hi.z, q.z) }
    }
    expect(dist3(p, { x: (lo.x + hi.x) / 2, y: (lo.y + hi.y) / 2, z: (lo.z + hi.z) / 2 })).toBeLessThan(1e-9)
  })
  it('an unknown key focuses nothing', () => {
    const { scene } = fixture()
    expect(focusPoint('b:nope', scene.entities)).toBeNull()
  })
})
