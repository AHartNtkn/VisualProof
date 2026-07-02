import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { buildFregeTheory } from '../../src/theories/frege'
import { buildLambdaTheory } from '../../src/theories/lambda'
import type { DiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { mkEngine } from '../../src/view/engine'
import { settle } from '../../src/view/relax'
import { paint, bubbleHues, highlightGroup, nextTheme, LIGHT, DARK, THEMES } from '../../src/view/paint'

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

describe('law 3 — boundary honesty: boundary wires exit the frame, internal singletons get an exists-stub', () => {
  it('a lone internal identity gets one exists-stub, no frame exit', () => {
    const h = new DiagramBuilder()
    h.termNode(h.root, p('\\x. x')) // its output is an internal singleton wire
    const d = h.build()
    const e = mkEngine(d, [])
    settle(e, 400)
    const shapes = paint(e, LIGHT)
    expect(shapes.filter((s) => s.kind === 'stub')).toHaveLength(1)
    expect(shapes.filter((s) => s.kind === 'exit')).toHaveLength(0)
  })

  it('a bundled side emits exactly one frame exit per boundary wire', () => {
    const nat = buildFregeTheory().relations.nat!
    const e = mkEngine(nat.diagram, nat.boundary)
    settle(e, 1200)
    const shapes = paint(e, LIGHT)
    expect(shapes.filter((s) => s.kind === 'exit')).toHaveLength(nat.boundary.length)
    expect(nat.boundary.length).toBeGreaterThan(0)
  })
})

describe('law 5 — linework coherence: wires and lambda-anatomy share stroke and width', () => {
  it('every wire bezier and every term-anatomy arc uses theme.wire at theme.wireW', () => {
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
    const beziers = shapes.filter((s) => s.kind === 'bezier')
    expect(beziers.length).toBeGreaterThan(0)
    for (const s of beziers) {
      if (s.kind !== 'bezier') continue
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
    const lightWire = paint(e, LIGHT).find((s) => s.kind === 'bezier')!
    const darkWire = paint(e, DARK).find((s) => s.kind === 'bezier')!
    expect(LIGHT.wire).not.toBe(DARK.wire)
    expect(lightWire.kind === 'bezier' && lightWire.stroke).toBe(LIGHT.wire)
    expect(darkWire.kind === 'bezier' && darkWire.stroke).toBe(DARK.wire)
    expect(lightWire.kind === 'bezier' && lightWire.glow).toBeNull()
    expect(darkWire.kind === 'bezier' && darkWire.glow).toBe(DARK.wire)
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
