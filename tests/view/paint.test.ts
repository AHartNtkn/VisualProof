import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { buildFregeTheory } from '../../src/theories/frege'
import { buildLambdaTheory } from '../../src/theories/lambda'
import type { DiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { mkEngine, frameBounds, frameSlots } from '../../src/view/engine'
import { settle } from '../../src/view/relax'
import { paint, bubbleHues, highlightGroup, nextTheme, LIGHT, DARK, THEMES } from '../../src/view/paint'
import { computeLegs } from '../../src/view/wires'

const p = (s: string) => parseTerm(s)

describe('law 2 — no text on lambda: labels only on ref-node discs', () => {
  it('emits exactly one label per ref, at the ref disc, and none over term anatomy', () => {
    const h = new DiagramBuilder()
    h.termNode(h.root, p('\\n. n')) // pure λ anatomy — no text of any kind
    h.ref(h.root, 'Nat', 1) // one ref disc
    const d = h.build()
    const e = mkEngine(d, [])
    settle(e, 400)
    const shapes = paint(e, LIGHT)
    const labels = shapes.filter((s) => s.kind === 'label')
    expect(labels).toHaveLength(1)
    expect(labels[0]!.kind === 'label' && labels[0]!.text).toBe('Nat')
    // term anatomy is present (arcs) yet carries zero text
    expect(shapes.some((s) => s.kind === 'arc')).toBe(true)
  })

  it('across both theories: every label sits on a ref-node disc; term anatomy emits no text and no disc', () => {
    const sides: DiagramWithBoundary[] = []
    for (const theory of [buildFregeTheory(), buildLambdaTheory()]) {
      for (const rel of Object.values(theory.relations)) sides.push(rel)
      for (const thm of theory.theorems) { sides.push(thm.lhs); sides.push(thm.rhs) }
    }
    for (const side of sides) {
      const e = mkEngine(side.diagram, side.boundary)
      settle(e, 200)
      const shapes = paint(e, LIGHT)
      const refPositions = [...e.bodies.values()]
        .filter((b) => b.kind === 'ref')
        .map((b) => b.pos)
      const labels = shapes.filter((s) => s.kind === 'label')
      // one label per ref, and never more
      expect(labels).toHaveLength(refPositions.length)
      // every label sits exactly on a ref-node disc centre
      for (const l of labels) {
        if (l.kind !== 'label') continue
        const onRef = refPositions.some((pos) => Math.hypot(pos.x - l.center.x, pos.y - l.center.y) < 1e-9)
        expect(onRef, `label '${l.text}' is not on a ref disc`).toBe(true)
      }
      // named discs (circles filled with the disc fill) are emitted only for
      // refs — a satellite would attach one to term anatomy off a ref centre
      const discs = shapes.filter((s) => s.kind === 'circle' && s.fill === LIGHT.discFill)
      expect(discs).toHaveLength(refPositions.length)
      for (const disc of discs) {
        if (disc.kind !== 'circle') continue
        const onRef = refPositions.some((pos) => Math.hypot(pos.x - disc.center.x, pos.y - disc.center.y) < 1e-9)
        expect(onRef, 'a named disc is not on a ref centre').toBe(true)
      }
    }
  })
})

describe('law 3 — boundary honesty: boundary wires connect INSIDE the frame, internal singletons get an exists-stub', () => {
  it('a lone internal identity gets one exists-stub and nothing at the frame', () => {
    const h = new DiagramBuilder()
    h.termNode(h.root, p('\\x. x')) // its output is an internal singleton wire
    const d = h.build()
    const e = mkEngine(d, [])
    settle(e, 400)
    const shapes = paint(e, LIGHT)
    expect(shapes.filter((s) => s.kind === 'stub')).toHaveLength(1)
  })

  it("a bundled side's boundary wires each reach a slot on the INSIDE of the frame — no shape outside it", () => {
    const nat = buildFregeTheory().relations.nat!
    const e = mkEngine(nat.diagram, nat.boundary)
    settle(e, 1200)
    expect(nat.boundary.length).toBeGreaterThan(0)
    const fb = frameBounds(e)!
    const slots = frameSlots(fb, nat.boundary.length)
    // every boundary wire's leg reaches its slot on the inner frame edge
    const legsByWid = new Map<string, { x: number; y: number }[][]>()
    for (const g of computeLegs(e)) { const a = legsByWid.get(g.leg.wid) ?? []; a.push(g.pts); legsByWid.set(g.leg.wid, a) }
    nat.boundary.forEach((wid, i) => {
      let best = Infinity
      for (const pts of legsByWid.get(wid)!) for (const end of [pts[0]!, pts[pts.length - 1]!]) {
        best = Math.min(best, Math.hypot(end.x - slots[i]!.point.x, end.y - slots[i]!.point.y))
      }
      expect(best, `boundary ${i} reaches slot ${i} on the inner frame edge`).toBeLessThan(1.5)
    })
    // NOTHING is drawn outside the frame: every painted point stays within the box
    for (const s of paint(e, LIGHT)) {
      const pts = s.kind === 'polyline' ? s.pts : s.kind === 'stub' ? [s.from, s.to] : []
      for (const pt of pts) {
        expect(pt.x, 'no painted wire point past the frame').toBeGreaterThanOrEqual(fb.minX - 1)
        expect(pt.x).toBeLessThanOrEqual(fb.maxX + 1)
        expect(pt.y).toBeGreaterThanOrEqual(fb.minY - 1)
        expect(pt.y).toBeLessThanOrEqual(fb.maxY + 1)
      }
    }
  })
})

describe('frame pip — a rim dot marks boundary slot 0 when >= 2 boundary wires', () => {
  // The frame is the sheet's node; like a disc with >= 2 ordered ports it earns
  // a pip. The pip sits at slot 0 (the top-edge midpoint), from which the
  // boundary slots read clockwise. A 0/1-boundary sheet has nothing to order,
  // so it carries no pip. Device-pixel dot, drawn in the ink stroke.
  const dotsAt = (shapes: ReturnType<typeof paint>, pt: { x: number; y: number }) =>
    shapes.filter((s) => s.kind === 'dot' && Math.hypot(s.center.x - pt.x, s.center.y - pt.y) < 1e-6)

  it('two boundary wires: exactly one pip dot at slot 0 (the top-edge midpoint)', () => {
    const h = new DiagramBuilder()
    const a = h.termNode(h.root, p('x'))
    const b = h.termNode(h.root, p('y'))
    const w1 = h.wire(h.root, [{ node: a, port: { kind: 'freeVar', name: 'x' } }])
    const w2 = h.wire(h.root, [{ node: b, port: { kind: 'freeVar', name: 'y' } }])
    const e = mkEngine(h.build(), [w1, w2])
    settle(e, 800)
    const shapes = paint(e, LIGHT)
    const s0 = frameSlots(frameBounds(e)!, e.boundary.length)[0]!.point
    // slot 0 is on the top edge of the frame
    expect(s0.y).toBeCloseTo(frameBounds(e)!.minY, 6)
    const pip = dotsAt(shapes, s0)
    expect(pip).toHaveLength(1)
    expect(pip[0]!.kind === 'dot' && pip[0]!.fill).toBe(LIGHT.ink)
  })

  it('one boundary wire: no pip (nothing to order)', () => {
    const h = new DiagramBuilder()
    const a = h.termNode(h.root, p('x'))
    const w1 = h.wire(h.root, [{ node: a, port: { kind: 'freeVar', name: 'x' } }])
    const e = mkEngine(h.build(), [w1])
    settle(e, 800)
    const shapes = paint(e, LIGHT)
    const s0 = frameSlots(frameBounds(e)!, e.boundary.length)[0]!.point
    expect(dotsAt(shapes, s0)).toHaveLength(0)
  })

  it('no boundary wires: no pip', () => {
    const h = new DiagramBuilder()
    h.termNode(h.root, p('\\x. x'))
    const e = mkEngine(h.build(), [])
    settle(e, 400)
    const shapes = paint(e, LIGHT)
    // no boundary → the top-edge midpoint carries no dot
    const fb = frameBounds(e)!
    expect(dotsAt(shapes, { x: fb.center.x, y: fb.minY })).toHaveLength(0)
  })
})

describe('law 5 — linework coherence: wires and lambda-anatomy share stroke and width', () => {
  it('every wire polyline and every term-anatomy arc uses theme.wire at theme.wireW', () => {
    const h = new DiagramBuilder()
    const a = h.termNode(h.root, p('\\f. \\x. f (f x)'))
    const b = h.termNode(h.root, p('y'))
    h.wire(h.root, [
      { node: a, port: { kind: 'output' } },
      { node: b, port: { kind: 'freeVar', name: 'y' } },
    ])
    const d = h.build()
    const e = mkEngine(d, [])
    settle(e, 600)
    const shapes = paint(e, LIGHT)
    // plan 22: a wire leg IS its traced θ-quadratic polyline (no spline fit)
    const wires = shapes.filter((s) => s.kind === 'polyline')
    expect(wires.length).toBeGreaterThan(0)
    for (const s of wires) {
      if (s.kind !== 'polyline') continue
      expect(s.stroke).toBe(LIGHT.wire)
      expect(s.width).toBe(LIGHT.wireW)
    }
    // no atoms here, so ALL anatomy arcs must be the shared linework
    const arcs = shapes.filter((s) => s.kind === 'arc')
    expect(arcs.length).toBeGreaterThan(0)
    for (const s of arcs) {
      if (s.kind !== 'arc') continue
      expect(s.stroke).toBe(LIGHT.wire)
      expect(s.width).toBe(LIGHT.wireW)
    }
  })
})

describe('law 6 — colour codes binder identity, and Dark glows the bubble ring like its atoms', () => {
  const bubbleAtom = () => {
    const h = new DiagramBuilder()
    const bub = h.bubble(h.root, 1)
    h.atom(bub, bub)
    const d = h.build()
    const e = mkEngine(d, [])
    settle(e, 400)
    return { d, e, bub }
  }

  it('atom strokes and the bubble ring both derive from the per-bubble hue', () => {
    const { d, e, bub } = bubbleAtom()
    const hue = bubbleHues(d, LIGHT.bubbleLightness).get(bub)!
    const shapes = paint(e, LIGHT)
    const ring = shapes.filter((s) => s.kind === 'circle' && s.fill === null && s.stroke === hue)
    expect(ring).toHaveLength(1)
    const atomArcs = shapes.filter((s) => s.kind === 'arc' && s.stroke === hue)
    expect(atomArcs.length).toBeGreaterThan(0)
  })

  it('Dark: bubble ring AND atom anatomy glow in the binder hue; Light does not glow', () => {
    const { d, e, bub } = bubbleAtom()
    const darkShapes = paint(e, DARK)
    const darkHue = bubbleHues(d, DARK.bubbleLightness).get(bub)!
    const darkRing = darkShapes.find((s) => s.kind === 'circle' && s.fill === null && s.stroke === darkHue)!
    expect(darkRing.kind === 'circle' && darkRing.glow).toBe(darkHue)
    const darkAtomArc = darkShapes.find((s) => s.kind === 'arc' && s.stroke === darkHue)!
    expect(darkAtomArc.kind === 'arc' && darkAtomArc.glow).toBe(darkHue)

    const lightShapes = paint(e, LIGHT)
    const lightHue = bubbleHues(d, LIGHT.bubbleLightness).get(bub)!
    const lightRing = lightShapes.find((s) => s.kind === 'circle' && s.fill === null && s.stroke === lightHue)!
    expect(lightRing.kind === 'circle' && lightRing.glow).toBeNull()
    const lightAtomArc = lightShapes.find((s) => s.kind === 'arc' && s.stroke === lightHue)!
    expect(lightAtomArc.kind === 'arc' && lightAtomArc.glow).toBeNull()
  })

  it('ships the two first-class themes', () => {
    expect(THEMES).toHaveLength(2)
    expect(THEMES.map((t) => t.name)).toEqual([LIGHT.name, DARK.name])
    expect(LIGHT.wireGlow).toBe(false)
    expect(DARK.wireGlow).toBe(true)
  })
})

describe('theme toggle', () => {
  it('nextTheme flips between the two first-class themes', () => {
    expect(nextTheme(LIGHT)).toBe(DARK)
    expect(nextTheme(DARK)).toBe(LIGHT)
  })

  it('toggling changes the emitted wire styles (colour + glow)', () => {
    const h = new DiagramBuilder()
    const a = h.termNode(h.root, p('\\x. x'))
    const b = h.termNode(h.root, p('y'))
    h.wire(h.root, [
      { node: a, port: { kind: 'output' } },
      { node: b, port: { kind: 'freeVar', name: 'y' } },
    ])
    const e = mkEngine(h.build(), [])
    settle(e, 400)
    const lightWire = paint(e, LIGHT).find((s) => s.kind === 'polyline')!
    const darkWire = paint(e, DARK).find((s) => s.kind === 'polyline')!
    expect(LIGHT.wire).not.toBe(DARK.wire)
    expect(lightWire.kind === 'polyline' && lightWire.stroke).toBe(LIGHT.wire)
    expect(darkWire.kind === 'polyline' && darkWire.stroke).toBe(DARK.wire)
    expect(lightWire.kind === 'polyline' && lightWire.glow).toBeNull()
    expect(darkWire.kind === 'polyline' && darkWire.glow).toBe(DARK.wire)
  })
})

describe('hover-group highlight', () => {
  const grp = () => {
    const h = new DiagramBuilder()
    const bub = h.bubble(h.root, 1)
    h.atom(bub, bub)
    h.atom(bub, bub)
    const d = h.build()
    const e = mkEngine(d, [])
    settle(e, 400)
    return { d, e, bub }
  }

  it('brightens the bubble ring and every bound atom in the shared (brighter) hue', () => {
    const { d, e, bub } = grp()
    const base = bubbleHues(d, DARK.bubbleLightness).get(bub)!
    const shapes = highlightGroup(e, DARK, bub)
    const rings = shapes.filter((s) => s.kind === 'circle')
    expect(rings).toHaveLength(1)
    const ring = rings[0]!
    if (ring.kind !== 'circle') throw new Error('unreachable')
    expect(ring.stroke).not.toBe(base) // same hue family, brighter — not the base
    expect(ring.stroke!.startsWith('hsl')).toBe(true)
    const arcs = shapes.filter((s) => s.kind === 'arc')
    expect(arcs.length).toBeGreaterThan(0) // both atoms' outlines
    for (const a of arcs) if (a.kind === 'arc') expect(a.stroke).toBe(ring.stroke) // one shared hue
  })

  it('glows in Dark, not in Light; empty for a non-bubble region', () => {
    const { e, bub } = grp()
    const dark = highlightGroup(e, DARK, bub).find((s) => s.kind === 'circle')!
    const light = highlightGroup(e, LIGHT, bub).find((s) => s.kind === 'circle')!
    expect(dark.kind === 'circle' && dark.glow).not.toBeNull()
    expect(light.kind === 'circle' && light.glow).toBeNull()
    expect(highlightGroup(e, DARK, e.d.root)).toEqual([]) // the sheet is not a bubble group
  })
})

describe('port-order pip — a rim dot marks port a0 on nodes with ordered ports', () => {
  // Live feel report: nothing marked which leg of an n-ary relation is which,
  // and the first attempt (world-unit anatomy tick) was invisible at fitted
  // zoom and never painted for refs at all. The pip is a device-pixel DOT
  // (junction-dot family) on the drawn rim at port a0's angle, rotating with
  // the body; ports read clockwise from it.
  const p2 = (s: string) => parseTerm(s)
  const build = (arity: number) => {
    const h = new DiagramBuilder()
    const ref = h.ref(h.root, 'rel', arity)
    for (let i = 0; i < arity; i++) h.wire(h.root, [{ node: ref, port: { kind: 'arg', index: i } }])
    const e = mkEngine(h.build(), [])
    settle(e, 200)
    return { e, ref }
  }
  it('a ternary ref carries exactly one pip dot on its rim at the a0 angle', () => {
    const { e, ref } = build(3)
    const b = e.bodies.get(ref)!
    const shapes = paint(e, LIGHT)
    const rim = 5.5
    const expected = { x: b.pos.x + Math.cos(b.theta + Math.PI / 2) * rim, y: b.pos.y + Math.sin(b.theta + Math.PI / 2) * rim }
    const pips = shapes.filter((s) => s.kind === 'dot' && Math.hypot(s.center.x - expected.x, s.center.y - expected.y) < 1e-6)
    expect(pips).toHaveLength(1)
  })
  it('a unary ref carries one pip marking its single port at the a0 angle', () => {
    // A single-port node still gets a pip: it marks WHERE the wire attaches, so the
    // attachment is visible even when the wire routes around the disc (USER report:
    // the port marker was missing and the connection point was ambiguous).
    const { e, ref } = build(1)
    const b = e.bodies.get(ref)!
    const shapes = paint(e, LIGHT)
    const rim = 5.5
    const expected = { x: b.pos.x + Math.cos(b.theta + Math.PI / 2) * rim, y: b.pos.y + Math.sin(b.theta + Math.PI / 2) * rim }
    const pips = shapes.filter((s) => s.kind === 'dot' && Math.hypot(s.center.x - expected.x, s.center.y - expected.y) < 1e-6)
    expect(pips).toHaveLength(1)
  })
  it('an atom bound to an arity-2 bubble carries a pip in its own stroke', () => {
    const h = new DiagramBuilder()
    const bub = h.bubble(h.root, 2)
    const a = h.atom(bub, bub)
    void p2
    const e = mkEngine(h.build(), [])
    settle(e, 200)
    const b = e.bodies.get(a)!
    const shapes = paint(e, LIGHT)
    const rim = 2 * 2 // atom rail radius x atom ascale
    const expected = { x: b.pos.x + Math.cos(b.theta + Math.PI / 2) * rim, y: b.pos.y + Math.sin(b.theta + Math.PI / 2) * rim }
    const pips = shapes.filter((s) => s.kind === 'dot' && Math.hypot(s.center.x - expected.x, s.center.y - expected.y) < 1e-6)
    expect(pips).toHaveLength(1)
  })
})
