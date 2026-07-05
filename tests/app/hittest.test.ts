import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkEngine, recomputeRegions, legPaths, settle, boundaryExits, existentialStubs } from '../../src/view/index'
import type { Vec2 } from '../../src/view/index'
import { buildFregeTheory } from '../../src/theories/frege'
import { vec } from '../../src/view/vec'
import { hitTest, dragTarget, buildSelection } from '../../src/app/hittest'

const p = (s: string) => parseTerm(s)

/** A point ON a traced leg polyline (plan 22: the polyline IS the wire), its
    midpoint sample — guaranteed on the drawn curve, clear of the end discs. */
function midOf(pts: readonly Vec2[]): { x: number; y: number } {
  return pts[Math.floor(pts.length / 2)]!
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
  // loose-end ∃ bodies are bodies too — place them beside their nodes so the
  // hand-built geometry stays fully deliberate
  for (const [wid, w] of Object.entries(d.wires)) {
    const j = e.bodies.get(`j:${wid}`)
    if (j) { const at = e.bodies.get(w.endpoints[0]!.node)!.pos; j.pos = vec(at.x + 12, at.y + 8) }
  }
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
    const pts = legPaths(e2).find((l) => l.wid === w)!.pts
    const mid = midOf(pts) // guaranteed on the traced leg, clear of both discs
    expect(hitTest(e2, mid)).toEqual({ kind: 'wire', id: w })
  })

  it('returns null in empty space', () => {
    const { e } = setup()
    expect(hitTest(e, vec(500, 500))).toBeNull()
  })
})

describe('dragTarget — what a press-and-drag grabs', () => {
  it('a point inside a node disc grabs that body', () => {
    const { n, e } = setup()
    expect(dragTarget(e, vec(1, 1))).toEqual({ kind: 'body', id: n })
  })

  it('a point on an ∃ dot grabs its homed body (clicks resolve it to the wire, drags do not)', () => {
    // PLAN 21: hub junction bodies are gone — the grabbable junction-kind
    // bodies are the homed wire ends (the ∃ dots), which stay independently
    // manipulable (loose-ends law)
    const h2 = new DiagramBuilder()
    const a = h2.termNode(h2.root, p('\\x. x'))
    const w = h2.wire(h2.root, [{ node: a, port: { kind: 'output' } }])
    const e2 = mkEngine(h2.build(), [])
    settle(e2, 2600) // the ∃ dot parks just outside the disc's clearance once settled
    const j = e2.bodies.get(e2.wires.get(w)!.tipBodyId!)!
    expect(hitTest(e2, j.pos)).toEqual({ kind: 'wire', id: w })
    expect(dragTarget(e2, j.pos)).toEqual({ kind: 'body', id: j.id })
  })

  it('a point inside a region (off every disc) grabs the region', () => {
    const { cut, e } = setup()
    const g = e.regions.get(cut)!
    const probe = vec(g.center.x - g.radius + 1, g.center.y)
    expect(dragTarget(e, probe)).toEqual({ kind: 'region', id: cut })
  })

  it('empty sheet space grabs nothing — the background is not draggable', () => {
    const { e } = setup()
    expect(dragTarget(e, vec(500, 500))).toBeNull()
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

describe('engine hit targets (junctions, frame exits → existing vocabulary)', () => {
  it('a click on a branch junction resolves to its wire (the hub is the wire\'s own point)', () => {
    const h = new DiagramBuilder()
    const a = h.termNode(h.root, p('x'))
    const b = h.termNode(h.root, p('x'))
    const c = h.termNode(h.root, p('x'))
    const w = h.wire(h.root, [
      { node: a, port: { kind: 'freeVar', name: 'x' } },
      { node: b, port: { kind: 'freeVar', name: 'x' } },
      { node: c, port: { kind: 'freeVar', name: 'x' } },
    ])
    const e = mkEngine(h.build(), [])
    settle(e, 2600)
    recomputeRegions(e)
    // a same-scope k-ary junction is a wire-owned hub POINT; every leg ends on
    // it, so a click there lands on the traced legs and resolves to the wire
    const hub = e.wires.get(w)!.hub!
    expect(hub.kind).toBe('point')
    expect(hitTest(e, hub.kind === 'point' ? hub.pos : e.bodies.get(hub.bodyId)!.pos)).toEqual({ kind: 'wire', id: w })
  })

  it('a click on an existential stub resolves to its internal wire', () => {
    // A lone internal identity node: its output is a genuine internal singleton
    // wire, painted as an ∃ stub. The stub is a painted target, so it must be
    // hittable (paint/hit parity) and resolve to that wire.
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('\\x. x'))
    const d = h.build()
    const e = mkEngine(d, [])
    e.bodies.get(n)!.pos = vec(0, 0)
    const loose = [...e.bodies.values()].find((b) => b.kind === 'junction')!
    loose.pos = vec(30, 0) // the ∃ dot is its own body — place it clear of the node disc
    recomputeRegions(e)
    const stub = existentialStubs(e)[0]!
    expect(stub).toBeDefined()
    expect(hitTest(e, stub.dot)).toEqual({ kind: 'wire', id: stub.wid })
  })

  it('a click on a frame exit resolves to its boundary wire', () => {
    const nat = buildFregeTheory().relations.nat!
    const e = mkEngine(nat.diagram, nat.boundary)
    settle(e, 1200)
    const ex = boundaryExits(e)[0]!
    expect(ex).toBeDefined()
    // the tick sits at the frame edge, on the exit spline, clear of nodes/regions
    expect(hitTest(e, ex.tick.center)).toEqual({ kind: 'wire', id: ex.wid })
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
