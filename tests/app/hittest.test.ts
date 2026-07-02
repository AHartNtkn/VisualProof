import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkEngine, recomputeRegions, legPaths } from '../../src/view/index'
import type { WirePath } from '../../src/view/index'
import { vec } from '../../src/view/vec'
import { hitTest, buildSelection } from '../../src/app/hittest'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

/** Point on a cubic Bézier at parameter t. */
function bezierAt(path: WirePath, t: number): { x: number; y: number } {
  const u = 1 - t
  const a = u * u * u, b = 3 * u * u * t, c = 3 * u * t * t, d = t * t * t
  return {
    x: a * path.from.x + b * path.c1.x + c * path.c2.x + d * path.to.x,
    y: a * path.from.y + b * path.c1.y + c * path.c2.y + d * path.to.y,
  }
}

function setup() {
  const h = new DiagramBuilder()
  const n = h.termNode(h.root, p('\\x. x'))
  const cut = h.cut(h.root)
  const m = h.termNode(cut, p('\\z. z')) // no free vars: its only loose end is the +x output stub
  const d = h.build()
  const e = mkEngine(d, [])
  e.bodies.get(n)!.pos = vec(0, 0)
  e.bodies.get(m)!.pos = vec(60, 0)
  recomputeRegions(e)
  return { d, n, cut, m, e }
}

describe('hitTest', () => {
  it('resolves a node when the point is inside its disc', () => {
    const { n, e } = setup()
    expect(hitTest(e, vec(1, 1))).toEqual({ kind: 'node', id: n })
  })

  it('resolves the smallest containing region otherwise', () => {
    const { cut, e } = setup()
    const g = e.regions.get(cut)!
    // probe the -x edge, clear of the node's +x output stub
    const probe = vec(g.center.x - g.radius + 1, g.center.y)
    expect(hitTest(e, probe)).toEqual({ kind: 'region', id: cut })
  })

  it('resolves a wire near its spline', () => {
    const h2 = new DiagramBuilder()
    const a = h2.termNode(h2.root, p('\\x. x'))
    const b = h2.termNode(h2.root, p('y'))
    const w = h2.wire(h2.root, [
      { node: a, port: { kind: 'output' } },
      { node: b, port: { kind: 'freeVar', name: 'y' } },
    ])
    const d2 = h2.build()
    const e2 = mkEngine(d2, [])
    e2.bodies.get(a)!.pos = vec(0, 0)
    e2.bodies.get(b)!.pos = vec(80, 0)
    recomputeRegions(e2)
    const path = legPaths(e2).find((l) => l.wid === w)!.path
    const mid = bezierAt(path, 0.5) // guaranteed on the spline, clear of both discs
    expect(hitTest(e2, mid)).toEqual({ kind: 'wire', id: w })
  })

  it('returns null in empty space', () => {
    const { e } = setup()
    expect(hitTest(e, vec(500, 500))).toBeNull()
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

describe('nested-region precedence', () => {
  it('the SMALLEST containing region wins', () => {
    const h = new DiagramBuilder()
    const outer = h.cut(h.root)
    const inner = h.cut(outer)
    const m = h.termNode(inner, p('\\z. z')) // only loose end is the +x output stub
    const d = h.build()
    const e = mkEngine(d, [])
    e.bodies.get(m)!.pos = vec(0, 0)
    recomputeRegions(e)
    const innerCircle = e.regions.get(inner)!
    // probe the -x edge, clear of the +x output stub
    const probe = vec(innerCircle.center.x - innerCircle.radius + 0.5, innerCircle.center.y)
    expect(hitTest(e, probe)).toEqual({ kind: 'region', id: inner })
  })
})
