import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { buildScene } from '../../src/view/scene'
import { vec } from '../../src/view/vec'
import { hitTest, buildSelection } from '../../src/app/hittest'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

function setup() {
  const h = new DiagramBuilder()
  const n = h.termNode(h.root, p('\\x. x'))
  const cut = h.cut(h.root)
  const m = h.termNode(cut, p('y'))
  const d = h.build()
  const positions = new Map([[n, vec(0, 0)], [m, vec(60, 0)]])
  const scene = buildScene(d, positions)
  return { d, n, cut, m, scene }
}

describe('hitTest', () => {
  it('resolves a node when the point is inside its outer radius', () => {
    const { n, scene } = setup()
    const hit = hitTest(scene, vec(1, 1))
    expect(hit).toEqual({ kind: 'node', id: n })
  })

  it('resolves the smallest containing region otherwise', () => {
    const { cut, scene } = setup()
    const region = scene.regions.find((r) => r.id === cut)!
    const probe = vec(region.center.x + region.radius - 1, region.center.y)
    const hit = hitTest(scene, probe)
    expect(hit).toEqual({ kind: 'region', id: cut })
  })

  it('resolves a wire near a spoke segment', () => {
    const { d, n, m } = setup()
    const h2 = new DiagramBuilder()
    const a = h2.termNode(h2.root, p('\\x. x'))
    const b = h2.termNode(h2.root, p('y'))
    const w = h2.wire(h2.root, [
      { node: a, port: { kind: 'output' } },
      { node: b, port: { kind: 'freeVar', name: 'y' } },
    ])
    const d2 = h2.build()
    const scene2 = buildScene(d2, new Map([[a, vec(0, 0)], [b, vec(80, 0)]]))
    const star = scene2.wires.find((x) => x.id === w)!
    const mid = vec((star.hub.x + star.spokes[0]!.x) / 2, (star.hub.y + star.spokes[0]!.y) / 2)
    expect(hitTest(scene2, mid)).toEqual({ kind: 'wire', id: w })
    void d
    void n
    void m
  })

  it('returns null in empty space', () => {
    const { scene } = setup()
    expect(hitTest(scene, vec(500, 500))).toBeNull()
  })
})

describe('buildSelection', () => {
  it('derives the anchor and partitions items into nodes and subtree roots', () => {
    const { d, n, cut } = setup()
    const sel = buildSelection(d, [{ kind: 'node', id: n }, { kind: 'region', id: cut }])
    expect(sel.region).toBe(d.root)
    expect(sel.nodes).toEqual([n])
    expect(sel.regions).toEqual([cut])
  })

  it('refuses mixed-depth picks with an instructive message', () => {
    const { d, n, m } = setup()
    expect(() => buildSelection(d, [{ kind: 'node', id: n }, { kind: 'node', id: m }]))
      .toThrowError(/select the enclosing cut instead/)
  })
})
