import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { trompGrid } from '../../src/view/tromp'
import { bendGrid, atomGeometry, GAP_ANGLE } from '../../src/view/bend'
import { length } from '../../src/view/vec'

const p = (s: string) => parseTerm(s)

describe('bendGrid', () => {
  it('maps binder bars to rim arcs, outermost binder outermost', () => {
    const g = bendGrid(trompGrid(p('\\x. \\y. x')))
    const lamArcs = g.arcs.filter((a) => a.kind === 'lam')
    expect(lamArcs).toHaveLength(2)
    const outer = lamArcs.find((a) => a.hueRow === 0)!
    const inner = lamArcs.find((a) => a.hueRow === 1)!
    expect(outer.r).toBeGreaterThan(inner.r)
  })

  it('keeps every angle inside the C (the gap is empty)', () => {
    const g = bendGrid(trompGrid(p('\\f. \\x. f (f x)')))
    const lo = GAP_ANGLE / 2
    const hi = 2 * Math.PI - GAP_ANGLE / 2
    for (const a of g.arcs) {
      expect(a.a0).toBeGreaterThanOrEqual(lo)
      expect(a.a1).toBeLessThanOrEqual(hi)
    }
    for (const r of g.radials) {
      expect(r.angle).toBeGreaterThanOrEqual(lo)
      expect(r.angle).toBeLessThanOrEqual(hi)
    }
  })

  it('port anchors pierce the rim radially: anchor radius exceeds every arc radius', () => {
    const g = bendGrid(trompGrid(p('y (z y)')))
    const maxArcR = Math.max(...g.arcs.map((a) => a.r))
    for (const name of ['y', 'z']) {
      expect(length(g.portAnchors[name]!)).toBeGreaterThan(maxArcR)
    }
  })

  it('the output anchor sits in the gap at angle 0, outside the rim', () => {
    const g = bendGrid(trompGrid(p('\\x. x')))
    expect(g.outputAnchor.y).toBeCloseTo(0, 10)
    expect(g.outputAnchor.x).toBeGreaterThan(0)
    const maxArcR = Math.max(...g.arcs.map((a) => a.r))
    expect(length(g.outputAnchor)).toBeGreaterThan(maxArcR)
    // the exit path: an innermost arc to the gap edge plus a straight line out
    expect(g.exitArc).not.toBeNull()
    expect(g.exitLine).toHaveLength(2)
  })

  it('var radials inherit their binder row for hue identity', () => {
    const g = bendGrid(trompGrid(p('\\x. \\y. x')))
    const varRadial = g.radials.find((r) => r.kind === 'var')!
    expect(varRadial.hueRow).toBe(0) // bound by the outer binder
  })

  it('all radii stay positive (the disc center is never crossed)', () => {
    const g = bendGrid(trompGrid(p('(\\x. x x) (\\y. y y)')))
    for (const a of g.arcs) expect(a.r).toBeGreaterThan(0)
    for (const r of g.radials) {
      expect(r.r0).toBeGreaterThan(0)
      expect(r.r1).toBeGreaterThan(0)
    }
  })
})

describe('atomGeometry', () => {
  it('spreads arg anchors evenly and scales with arity', () => {
    const g2 = atomGeometry(2)
    expect(Object.keys(g2.portAnchors)).toEqual(['a0', 'a1'])
    const d0 = length(g2.portAnchors['a0']!)
    const d1 = length(g2.portAnchors['a1']!)
    expect(d0).toBeCloseTo(d1, 10)
    expect(atomGeometry(0).arcs.length).toBeGreaterThan(0) // still a visible disc
  })

  it('emits no exit line (law 4: refs/atoms have no term output, so no second leg)', () => {
    expect(atomGeometry(2).exitLine).toBeNull()
    expect(atomGeometry(0).exitLine).toBeNull()
  })
})

describe('port-order pip (n-ary discs, n >= 2)', () => {
  // Which port is a0 is invisible on a featureless disc once the body rotates.
  // The pip — a short radial tick INSIDE the rail at a0's angle — marks the
  // first port; ports then read clockwise (canvas y-down) from the pip.
  it('arity >= 2 discs carry exactly one inner pip tick at the a0 angle', () => {
    for (const arity of [2, 3, 5]) {
      const g = atomGeometry(arity)
      const rail = g.arcs[0]!.r
      const a0angle = Math.PI / 2
      const pips = g.radials.filter((r) => r.r1 <= rail && Math.abs(r.angle - a0angle) < 1e-9)
      expect(pips, `arity ${arity}`).toHaveLength(1)
      expect(pips[0]!.r0).toBeGreaterThan(0)
      expect(pips[0]!.r1).toBeLessThan(rail)
    }
  })

  it('arity <= 1 discs carry no pip (nothing to disambiguate)', () => {
    for (const arity of [0, 1]) {
      const rail = atomGeometry(arity).arcs[0]!.r
      const pips = atomGeometry(arity).radials.filter((r) => r.r1 <= rail)
      expect(pips, `arity ${arity}`).toHaveLength(0)
    }
  })

  it('ports order clockwise from the pip: anchor i sits at pip-angle + i*(2pi/n)', () => {
    // canvas coordinates are y-down, so increasing angle IS clockwise on screen
    for (const arity of [2, 3, 4]) {
      const g = atomGeometry(arity)
      for (let i = 0; i < arity; i++) {
        const a = g.portAnchors[`a${i}`]!
        const angle = Math.atan2(a.y, a.x)
        const expected = Math.atan2(Math.sin(Math.PI / 2 + (i * 2 * Math.PI) / arity), Math.cos(Math.PI / 2 + (i * 2 * Math.PI) / arity))
        expect(angle, `arity ${arity} port ${i}`).toBeCloseTo(expected, 9)
      }
    }
  })
})
