import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { buildScene } from '../../src/view/scene'
import { vec, length, sub } from '../../src/view/vec'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

function host() {
  const h = new DiagramBuilder()
  const n = h.termNode(h.root, p('y'))
  const cut = h.cut(h.root)
  const m = h.termNode(cut, p('\\x. x'))
  const w = h.wire(h.root, [
    { node: n, port: { kind: 'freeVar', name: 'y' } },
    { node: m, port: { kind: 'output' } },
  ])
  const bub = h.bubble(cut, 1)
  const atom = h.atom(bub, bub)
  h.wire(cut, [{ node: atom, port: { kind: 'arg', index: 0 } }])
  return { d: h.build(), n, cut, m, w, bub, atom }
}

describe('buildScene', () => {
  it('derives region circles bottom-up: every region encloses its contents', () => {
    const { d, n, m, atom, cut, bub } = host()
    const pos = new Map([[n, vec(0, 0)], [m, vec(40, 0)], [atom, vec(60, 0)]])
    const scene = buildScene(d, pos)
    const byId = new Map(scene.regions.map((r) => [r.id, r]))
    for (const sn of scene.nodes) {
      const region = byId.get(d.nodes[sn.id]!.region)!
      const need = length(sub(sn.center, region.center)) + sn.geometry.outerRadius
      expect(region.radius).toBeGreaterThanOrEqual(need)
    }
    // nesting: the bubble circle lies inside the cut circle
    const cutCircle = byId.get(cut)!
    const bubCircle = byId.get(bub)!
    const dist = length(sub(bubCircle.center, cutCircle.center))
    expect(dist + bubCircle.radius).toBeLessThanOrEqual(cutCircle.radius + 1e-9)
  })

  it('shades exactly the negative regions', () => {
    const { d, n, m, atom } = host()
    const pos = new Map([[n, vec(0, 0)], [m, vec(40, 0)], [atom, vec(60, 0)]])
    const scene = buildScene(d, pos)
    for (const r of scene.regions) {
      const expected = d.regions[r.id]!.kind === 'cut' // depth-1 cut is the only negative region here
      expect(r.shaded).toBe(expected)
    }
  })

  it('wire stars pass through the endpoint anchors', () => {
    const { d, n, m, atom, w } = host()
    const pos = new Map([[n, vec(0, 0)], [m, vec(40, 0)], [atom, vec(60, 0)]])
    const scene = buildScene(d, pos)
    const star = scene.wires.find((x) => x.id === w)!
    expect(star.spokes).toHaveLength(2)
    // the hub is the centroid of the spokes
    const cx = (star.spokes[0]!.x + star.spokes[1]!.x) / 2
    expect(star.hub.x).toBeCloseTo(cx, 10)
  })

  it('zero-endpoint wires render as a hub at their scope center', () => {
    const h = new DiagramBuilder()
    h.wire(h.root, [])
    const d = h.build()
    const scene = buildScene(d, new Map())
    expect(scene.wires).toHaveLength(1)
    expect(scene.wires[0]!.spokes).toHaveLength(0)
  })

  it('rejects positions for unknown nodes and missing positions, loudly', () => {
    const { d, n, m, atom } = host()
    expect(() => buildScene(d, new Map([[n, vec(0, 0)], [m, vec(1, 0)]])))
      .toThrowError(new RegExp(`no position for node '${atom}'`))
    expect(() => buildScene(d, new Map([[n, vec(0, 0)], [m, vec(1, 0)], [atom, vec(2, 0)], ['ghost', vec(3, 0)]])))
      .toThrowError(/position for unknown node 'ghost'/)
  })
})
