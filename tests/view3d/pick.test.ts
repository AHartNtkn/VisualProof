import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { relSig, IOTA } from '../../src/kernel/diagram/sig'
import { diagramSpec } from '../../src/view3d/spec'
import { scene3 } from '../../src/view3d/scene'
import { expandHover } from '../../src/view3d/pick'

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
    const got = expandHover(`b:${c1}`, spec, scene.entities)
    expect(got.has(`b:${c1}`)).toBe(true)
    expect(got.has(`b:${c2}`)).toBe(true)
    expect(got.has('b:r0')).toBe(false)
  })
  it('a ring expands to ring + its label + incident wire anchors (spec: hovering a node highlights its ring plus incident wire anchors)', () => {
    const { spec, scene, R, wPR, wST } = fixture()
    const got = expandHover(`r:${R}`, spec, scene.entities)
    expect(got.has(`r:${R}`)).toBe(true)
    expect(got.has(`l:${R}`)).toBe(true)
    const strandsOf = (wid: string) => scene.entities.filter((e) => e.kind === 'strand' && e.wire === wid).map((e) => e.key)
    const ownStrands = strandsOf(wPR)
    expect(ownStrands.length).toBeGreaterThan(0)
    for (const k of ownStrands) expect(got.has(k)).toBe(true)
    // The unrelated wire (S-T, touching neither P nor R) must NOT light up.
    for (const k of strandsOf(wST)) expect(got.has(k)).toBe(false)
  })
})
