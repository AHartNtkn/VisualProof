import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { trompGrid } from '../../src/view/tromp'
import { bendGrid, type NodeGeometry } from '../../src/view/bend'
import { polar } from '../../src/view/vec'
import { mkGeomMorph } from '../../src/view/morph'

const geomOf = (src: string): NodeGeometry => bendGrid(trompGrid(parseTerm(src)))

// the β chain the round-7 page plays: (λx. x x)(λy. y) → (λy. y)(λy. y) → λy. y
const gRedex = geomOf('(\\x. x x) (\\y. y)')
const gMid = geomOf('(\\y. y) (\\y. y)')
const gId = geomOf('\\y. y')
// free-variable churn: `f x` → `x` drops port f entirely
const gApp = geomOf('f x')
const gVar = geomOf('x')

const close = (a: number, b: number, eps = 1e-9): boolean => Math.abs(a - b) < eps

describe('mkGeomMorph endpoints', () => {
  it('p=0 reproduces every arc, radial, and port anchor of the source', () => {
    const m = mkGeomMorph(gRedex, gMid)
    const g0 = m(0)
    for (const a of gRedex.arcs) {
      expect(g0.arcs.some((x) => close(x.r, a.r) && close(x.a0, a.a0) && close(x.a1, a.a1)),
        `source arc r=${a.r} [${a.a0},${a.a1}] missing at p=0`).toBe(true)
    }
    for (const r of gRedex.radials) {
      expect(g0.radials.some((x) => close(x.angle, r.angle) && close(x.r0, r.r0) && close(x.r1, r.r1)),
        `source radial angle=${r.angle} missing at p=0`).toBe(true)
    }
    for (const [name, v] of Object.entries(gRedex.portAnchors)) {
      const w = g0.portAnchors[name]!
      expect(close(w.x, v.x) && close(w.y, v.y), `anchor '${name}' moved at p=0`).toBe(true)
    }
    expect(close(g0.outputAnchor.x, gRedex.outputAnchor.x)).toBe(true)
    expect(close(g0.outerRadius, gRedex.outerRadius)).toBe(true)
  })

  it('p=1 reproduces every arc, radial, and port anchor of the target', () => {
    const m = mkGeomMorph(gRedex, gMid)
    const g1 = m(1)
    for (const a of gMid.arcs) {
      expect(g1.arcs.some((x) => close(x.r, a.r) && close(x.a0, a.a0) && close(x.a1, a.a1)),
        `target arc r=${a.r} [${a.a0},${a.a1}] missing at p=1`).toBe(true)
    }
    for (const r of gMid.radials) {
      expect(g1.radials.some((x) => close(x.angle, r.angle) && close(x.r0, r.r0) && close(x.r1, r.r1)),
        `target radial angle=${r.angle} missing at p=1`).toBe(true)
    }
    for (const [name, v] of Object.entries(gMid.portAnchors)) {
      const w = g1.portAnchors[name]!
      expect(close(w.x, v.x) && close(w.y, v.y), `anchor '${name}' off target at p=1`).toBe(true)
    }
  })

  it('unmatched source pieces have collapsed to zero extent at p=1', () => {
    const m = mkGeomMorph(gRedex, gId)
    const g1 = m(1)
    // everything drawn at p=1 is either a target piece or has zero extent
    for (const a of g1.arcs) {
      const isTarget = gId.arcs.some((x) => close(x.r, a.r) && close(x.a0, a.a0) && close(x.a1, a.a1))
      expect(isTarget || close(a.a1 - a.a0, 0), `leftover arc with extent ${a.a1 - a.a0}`).toBe(true)
    }
    for (const r of g1.radials) {
      const isTarget = gId.radials.some((x) => close(x.angle, r.angle) && close(x.r0, r.r0) && close(x.r1, r.r1))
      expect(isTarget || close(r.r1 - r.r0, 0), `leftover radial with extent ${r.r1 - r.r0}`).toBe(true)
    }
  })
})

describe('mkGeomMorph wire-attachment invariant', () => {
  it('every port anchor is the tip of a drawn port rail at EVERY p', () => {
    for (const [from, to] of [[gRedex, gMid], [gMid, gId], [gApp, gVar]] as const) {
      const m = mkGeomMorph(from, to)
      for (const p of [0, 0.2, 0.4, 0.5, 0.6, 0.8, 1]) {
        const g = m(p)
        for (const [name, v] of Object.entries(g.portAnchors)) {
          const onRail = g.radials.some((r) => {
            if (r.kind !== 'port') return false
            const tip = polar(r.angle, r.r1)
            return close(tip.x, v.x) && close(tip.y, v.y)
          })
          expect(onRail, `anchor '${name}' off every rail tip at p=${p}`).toBe(true)
        }
      }
    }
  })

  it('a dying port rides its retracting rail (f x → x drops f continuously)', () => {
    const m = mkGeomMorph(gApp, gVar)
    expect(gVar.portAnchors['f']).toBeUndefined()
    const start = m(0).portAnchors['f']!
    const mid = m(0.5).portAnchors['f']!
    const end = m(1).portAnchors['f']!
    // it retracts monotonically toward the anatomy, never jumps
    const r0 = Math.hypot(start.x, start.y), r5 = Math.hypot(mid.x, mid.y), r1 = Math.hypot(end.x, end.y)
    expect(r5).toBeLessThan(r0)
    expect(r1).toBeLessThan(r5)
    // and lands on a zero-length rail (the port has fully vanished)
    const rail = m(1).radials.find((r) => r.kind === 'port' && close(polar(r.angle, r.r1).x, end.x) && close(polar(r.angle, r.r1).y, end.y))!
    expect(close(rail.r1 - rail.r0, 0)).toBe(true)
  })
})

describe('mkGeomMorph continuity', () => {
  it('no piece jumps: parameter step ε moves every endpoint O(ε)', () => {
    for (const [from, to] of [[gRedex, gMid], [gMid, gId], [gApp, gVar]] as const) {
      const m = mkGeomMorph(from, to)
      const EPS = 1e-3
      // scale bound: total travel over p∈[0,1] is bounded by the diagram
      // diameter, so an ε step may move a point at most diameter·ε — use a
      // generous constant multiple to keep the test principled, not tuned
      const bound = 4 * (from.outerRadius + to.outerRadius) * EPS
      for (const p of [0, 0.25, 0.5, 0.75, 1 - EPS]) {
        const a = m(p), b = m(p + EPS)
        expect(a.arcs.length).toBe(b.arcs.length)
        expect(a.radials.length).toBe(b.radials.length)
        a.arcs.forEach((x, i) => {
          const y = b.arcs[i]!
          expect(Math.abs(x.r - y.r) + Math.abs(x.a0 - y.a0) + Math.abs(x.a1 - y.a1)).toBeLessThan(bound)
        })
        a.radials.forEach((x, i) => {
          const y = b.radials[i]!
          expect(Math.abs(x.angle - y.angle) + Math.abs(x.r0 - y.r0) + Math.abs(x.r1 - y.r1)).toBeLessThan(bound)
        })
      }
    }
  })
})
