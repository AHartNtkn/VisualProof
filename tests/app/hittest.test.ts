import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkDiagram } from '../../src/kernel/diagram/diagram'
import { mkEngine, recomputeRegions, computeLegs, legPaths, settle, existentialStubs, frameBounds, frameSlots } from '../../src/view/index'
import type { Vec2 } from '../../src/view/index'
import { vec } from '../../src/view/vec'
import { hitTest, wireHitTest, wireManipulationHitTest, brushHitTest, dragTarget, buildSelection } from '../../src/interaction/hittest'

const p = (s: string) => parseTerm(s)
const viewport = (scale = 1) => ({ scale })

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

function unobstructedRegionPoint(
  e: ReturnType<typeof setup>['e'],
  regionId: string,
  ring: boolean,
): Vec2 {
  const region = e.regions.get(regionId)!
  const radii = ring
    ? [region.radius - 1]
    : [region.radius * 0.25, region.radius * 0.4, region.radius * 0.6]
  for (const radius of radii) {
    for (let i = 0; i < 64; i++) {
      const theta = i * Math.PI * 2 / 64
      const point = vec(region.center.x + Math.cos(theta) * radius, region.center.y + Math.sin(theta) * radius)
      const hit = hitTest(e, point, viewport())
      if (hit?.kind === 'region' && hit.id === regionId) return point
    }
  }
  throw new Error(`no unobstructed ${ring ? 'ring' : 'interior'} point for region '${regionId}'`)
}

function unobstructedOutsideRingPoint(e: ReturnType<typeof setup>['e'], regionId: string): Vec2 {
  const region = e.regions.get(regionId)!
  for (let i = 0; i < 64; i++) {
    const theta = i * Math.PI * 2 / 64
    const radius = region.radius + 1
    const point = vec(region.center.x + Math.cos(theta) * radius, region.center.y + Math.sin(theta) * radius)
    if (hitTest(e, point, viewport()) === null) return point
  }
  throw new Error(`no unobstructed outside-ring point for region '${regionId}'`)
}

describe('hitTest', () => {
  it('resolves a node when the point is inside its disc', () => {
    const { n, e } = setup()
    expect(hitTest(e, vec(1, 1), viewport())).toEqual({ kind: 'node', id: n })
  })

  it('resolves the smallest containing region otherwise', () => {
    const { cut, e } = setup()
    const g = e.regions.get(cut)!
    // probe the -x edge, clear of the node's +x output stub
    const probe = vec(g.center.x - g.radius + 1, g.center.y)
    expect(hitTest(e, probe, viewport())).toEqual({ kind: 'region', id: cut })
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
    expect(hitTest(e2, mid, viewport())).toEqual({ kind: 'wire', id: w })
  })

  it('lets a wire manipulation start where a dangling wire meets its node rim', () => {
    const h = new DiagramBuilder()
    const zero = h.ref(h.root, 'zero', 1)
    const d = h.build()
    const wire = Object.keys(d.wires)[0]!
    const e = mkEngine(d, [])
    e.bodies.get(zero)!.pos = vec(0, 0)
    e.bodies.get(e.wires.get(wire)!.tipBodyId!)!.pos = vec(80, 0)
    recomputeRegions(e)
    const bindPoint = legPaths(e).find((leg) => leg.wid === wire)!.pts[0]!

    expect(hitTest(e, bindPoint, viewport()), 'ordinary selection keeps node-first precedence').toEqual({ kind: 'node', id: zero })
    expect(wireHitTest(e, bindPoint, viewport()), 'wire manipulation sees every painted part of the line').toEqual({ kind: 'wire', id: wire })
  })

  it('distinguishes concrete endpoint legs from the trunk of one equality wire', () => {
    const h = new DiagramBuilder()
    const a = h.termNode(h.root, p('f x'))
    const b = h.termNode(h.root, p('f y'))
    const wire = h.wire(h.root, [
      { node: a, port: { kind: 'output' } },
      { node: b, port: { kind: 'output' } },
    ])
    const e = mkEngine(h.build(), [])
    e.bodies.get(a)!.pos = vec(-40, 0)
    e.bodies.get(b)!.pos = vec(40, 0)
    recomputeRegions(e)
    const path = computeLegs(e).find(({ leg }) => leg.wid === wire)!
    const pointFor = (node: string): Vec2 => path.leg.from.body === node ? path.pts[0]! : path.pts.at(-1)!

    expect(wireManipulationHitTest(e, pointFor(a), viewport())).toEqual({
      wire,
      endpoint: { node: a, port: { kind: 'output' } },
    })
    expect(wireManipulationHitTest(e, pointFor(b), viewport())).toEqual({
      wire,
      endpoint: { node: b, port: { kind: 'output' } },
    })
    expect(wireManipulationHitTest(e, midOf(path.pts), viewport())).toEqual({ wire, endpoint: null })
  })

  it('gives a painted semantic dot precedence over a coincident wire stroke', () => {
    const h = new DiagramBuilder()
    const a = h.termNode(h.root, p('x'))
    const b = h.termNode(h.root, p('x'))
    const stroke = h.wire(h.root, [
      { node: a, port: { kind: 'output' } },
      { node: b, port: { kind: 'freeVar', name: 'x' } },
    ])
    const marker = h.wire(h.root, [])
    const e = mkEngine(h.build(), [])
    e.bodies.get(a)!.pos = vec(-40, 0)
    e.bodies.get(b)!.pos = vec(40, 0)
    recomputeRegions(e)
    const point = midOf(legPaths(e).find((leg) => leg.wid === stroke)!.pts)
    e.bodies.get(`j:${marker}`)!.pos = point

    expect(wireHitTest(e, point, viewport())).toEqual({ kind: 'wire', id: marker })
  })

  it('returns null in empty space', () => {
    const { e } = setup()
    expect(hitTest(e, vec(500, 500), viewport())).toBeNull()
  })

  it('keeps one device-pixel wire halo at every viewport scale', () => {
    const wire = 'w'
    const d = mkDiagram({
      root: 'r0',
      regions: { r0: { kind: 'sheet' } },
      nodes: {
        a: { kind: 'ref', region: 'r0', defId: 'zero', arity: 1 },
        b: { kind: 'ref', region: 'r0', defId: 'zero', arity: 1 },
      },
      wires: {
        [wire]: {
          scope: 'r0',
          endpoints: [
            { node: 'a', port: { kind: 'arg', index: 0 } },
            { node: 'b', port: { kind: 'arg', index: 0 } },
          ],
        },
      },
    })
    const e = mkEngine(d, [])
    e.bodies.get('a')!.pos = vec(0, 0)
    e.bodies.get('b')!.pos = vec(80, 0)
    recomputeRegions(e)
    const pts = legPaths(e).find((leg) => leg.wid === wire)!.pts
    const i = Math.floor(pts.length / 2)
    const mid = pts[i]!
    const tangent = vec(pts[i + 1]!.x - pts[i - 1]!.x, pts[i + 1]!.y - pts[i - 1]!.y)
    const tangentLength = Math.hypot(tangent.x, tangent.y)
    const normal = vec(-tangent.y / tangentLength, tangent.x / tangentLength)

    for (const scale of [1, 2, 4]) {
      const inside = vec(mid.x + normal.x * 5 / scale, mid.y + normal.y * 5 / scale)
      const outside = vec(mid.x + normal.x * 7 / scale, mid.y + normal.y * 7 / scale)
      expect(wireHitTest(e, inside, viewport(scale)), `5 screen px at scale ${scale}`).toEqual({ kind: 'wire', id: wire })
      expect(wireHitTest(e, outside, viewport(scale)), `7 screen px at scale ${scale}`).toBeNull()
    }
  })

  it('chooses the nearest qualifying painted wire and breaks exact ties by stable identity', () => {
    const d = mkDiagram({
      root: 'r0',
      regions: { r0: { kind: 'sheet' } },
      // Deliberately insert `z` first: map traversal must not decide the hit.
      wires: {
        z: { scope: 'r0', endpoints: [] },
        a: { scope: 'r0', endpoints: [] },
      },
    })
    const e = mkEngine(d, [])
    e.bodies.get('j:z')!.pos = vec(0, 0)
    e.bodies.get('j:a')!.pos = vec(4, 0)
    recomputeRegions(e)
    expect(wireHitTest(e, vec(3, 0), viewport())).toEqual({ kind: 'wire', id: 'a' })

    e.bodies.get('j:a')!.pos = vec(0, 0)
    recomputeRegions(e)
    expect(wireHitTest(e, vec(0, 0), viewport())).toEqual({ kind: 'wire', id: 'a' })
  })

  it('refuses an invalid viewport scale instead of guessing hit units', () => {
    const { e } = setup()
    expect(() => hitTest(e, vec(0, 0), viewport(0))).toThrow(/finite and positive/)
    expect(() => wireHitTest(e, vec(0, 0), viewport(Number.NaN))).toThrow(/finite and positive/)
  })
})

describe('brushHitTest', () => {
  it('keeps stationary region clicks anywhere in the visible disc', () => {
    const { cut, e } = setup()
    const interior = unobstructedRegionPoint(e, cut, false)

    expect(brushHitTest(e, interior, viewport(), false)).toEqual({ kind: 'region', id: cut })
  })

  it('claims a moving region only within 1.5 world units of its ring', () => {
    const { cut, e } = setup()
    const onRing = unobstructedRegionPoint(e, cut, true)
    const outsideRing = unobstructedOutsideRingPoint(e, cut)
    const insideDisc = unobstructedRegionPoint(e, cut, false)

    expect(brushHitTest(e, onRing, viewport(), true)).toEqual({ kind: 'region', id: cut })
    expect(brushHitTest(e, outsideRing, viewport(), true)).toEqual({ kind: 'region', id: cut })
    expect(brushHitTest(e, insideDisc, viewport(), true)).toBeNull()
  })

  it('leaves moving node and wire hits unchanged', () => {
    const { n, e } = setup()
    expect(brushHitTest(e, vec(1, 1), viewport(), true)).toEqual({ kind: 'node', id: n })

    const h = new DiagramBuilder()
    const a = h.termNode(h.root, p('x'))
    const b = h.termNode(h.root, p('x'))
    const w = h.wire(h.root, [
      { node: a, port: { kind: 'output' } },
      { node: b, port: { kind: 'freeVar', name: 'x' } },
    ])
    const wireEngine = mkEngine(h.build(), [])
    wireEngine.bodies.get(a)!.pos = vec(-40, 0)
    wireEngine.bodies.get(b)!.pos = vec(40, 0)
    recomputeRegions(wireEngine)
    const point = midOf(legPaths(wireEngine).find((leg) => leg.wid === w)!.pts)

    expect(brushHitTest(wireEngine, point, viewport(), true)).toEqual({ kind: 'wire', id: w })
  })
})

describe('dragTarget — what a press-and-drag grabs', () => {
  it('a point inside a node disc grabs that body', () => {
    const { n, e } = setup()
    expect(dragTarget(e, vec(1, 1), viewport())).toEqual({ kind: 'body', id: n })
  })

  it('a point inside a region (off every disc) grabs the region', () => {
    const { cut, e } = setup()
    const g = e.regions.get(cut)!
    const probe = vec(g.center.x - g.radius + 1, g.center.y)
    expect(dragTarget(e, probe, viewport())).toEqual({ kind: 'region', id: cut })
  })

  it('empty sheet space grabs nothing — the background is not draggable', () => {
    const { e } = setup()
    expect(dragTarget(e, vec(500, 500), viewport())).toBeNull()
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
    expect(hitTest(e, stub.dot, viewport())).toEqual({ kind: 'wire', id: stub.wid })
  })

  it('clicking an endpointless boundary port at its drawn frame slot resolves to that wire', () => {
    const h = new DiagramBuilder()
    const w0 = h.wire(h.root, [])
    const w1 = h.wire(h.root, [])
    const e = mkEngine(h.build(), [w0, w1])
    settle(e, 20)
    e.slotShift = 1
    const slots = frameSlots(frameBounds(e)!, 2)

    expect(hitTest(e, slots[0]!.point, viewport()), 'hit geometry follows the proof-wide cyclic slot shift').toEqual({ kind: 'wire', id: w1 })
    expect(hitTest(e, slots[1]!.point, viewport())).toEqual({ kind: 'wire', id: w0 })
  })

  it('both boundary positions and the connecting path of one repeated wire hit the same identity', () => {
    const h = new DiagramBuilder()
    const shared = h.wire(h.root, [])
    const e = mkEngine(h.build(), [shared, shared])
    settle(e, 20)
    e.slotShift = 1
    const slots = frameSlots(frameBounds(e)!, 2)

    expect(hitTest(e, slots[0]!.point, viewport())).toEqual({ kind: 'wire', id: shared })
    expect(hitTest(e, slots[1]!.point, viewport())).toEqual({ kind: 'wire', id: shared })
    const path = legPaths(e).find((leg) => leg.wid === shared)!
    expect(hitTest(e, midOf(path.pts), viewport())).toEqual({ kind: 'wire', id: shared })
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
    expect(hitTest(e, probe, viewport())).toEqual({ kind: 'region', id: inner })
  })
})
