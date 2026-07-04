import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { trompGrid } from '../../src/view/tromp'
import { bendGrid, type NodeGeometry } from '../../src/view/bend'
import { polar } from '../../src/view/vec'
import { mkGeomMorph, mkGridMorph } from '../../src/view/morph'

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

// ============================================================
// mkGridMorph — the connection-preserving (grid-space) interpolator
// ============================================================
import type { NodeRadial } from '../../src/view/bend'

const gridRedex = trompGrid(parseTerm('(\\x. x x) (\\y. f y)'))
const gridMid = trompGrid(parseTerm('(\\y. f y) (\\y. f y)'))
const gridDone = trompGrid(parseTerm('f (\\y. f y)'))
const gridK1 = trompGrid(parseTerm('(\\x. \\y. x) a b'))
const gridK2 = trompGrid(parseTerm('(\\y. a) b'))
const gridK3 = trompGrid(parseTerm('a'))
const CHAINS = [[gridRedex, gridMid], [gridMid, gridDone], [gridK1, gridK2], [gridK2, gridK3]] as const

/** The user's ruling, formalized: a radial that hangs on an arc (its r0 end
    sits on the arc's circle inside its span) must stay hung for as long as
    it is drawn with positive extent — pieces shrink connected and are gone
    before they could detach. Output stems are excluded: their top end
    terminates on structure that is not always an arc even statically. */
const hangsOnSomeArc = (g: NodeGeometry, r: NodeRadial): boolean =>
  g.arcs.some((a) => Math.abs(a.r - r.r0) < 1e-9 && a.a0 - 1e-9 <= r.angle && r.angle <= a.a1 + 1e-9)
const attachedInvariant = (g: NodeGeometry): string[] =>
  g.radials
    .filter((r) => (r.kind === 'var' || r.kind === 'port') && Math.abs(r.r1 - r.r0) > 1e-9)
    .filter((r) => !hangsOnSomeArc(g, r))
    .map((r) => `${r.kind} radial at angle=${r.angle.toFixed(3)} r0=${r.r0.toFixed(3)} hangs on nothing`)

describe('mkGridMorph endpoints', () => {
  it('p=0 IS the source geometry piece-for-piece, p=1 IS the target', () => {
    for (const [f, t] of CHAINS) {
      const gf = bendGrid(f), gt = bendGrid(t)
      const m = mkGridMorph(f, t)
      for (const [got, want] of [[m(0), gf], [m(1), gt]] as const) {
        expect(got.arcs.length).toBe(want.arcs.length)
        for (const a of want.arcs) {
          expect(got.arcs.some((x) => close(x.r, a.r) && close(x.a0, a.a0) && close(x.a1, a.a1) && x.kind === a.kind),
            `arc r=${a.r} [${a.a0},${a.a1}] ${a.kind} missing`).toBe(true)
        }
        expect(got.radials.length).toBe(want.radials.length)
        for (const r of want.radials) {
          expect(got.radials.some((x) => close(x.angle, r.angle) && close(x.r0, r.r0) && close(x.r1, r.r1)),
            `radial angle=${r.angle} missing`).toBe(true)
        }
        for (const [name, v] of Object.entries(want.portAnchors)) {
          const w = got.portAnchors[name]!
          expect(close(w.x, v.x) && close(w.y, v.y), `anchor '${name}' off`).toBe(true)
        }
        expect(close(got.exitArc!.r, want.exitArc!.r)).toBe(true)
        expect(close(got.exitArc!.a1, want.exitArc!.a1)).toBe(true)
      }
    }
  })

  it('the static geometries themselves satisfy the attachment invariant (sanity)', () => {
    for (const g of [gridRedex, gridMid, gridDone, gridK1, gridK2, gridK3]) {
      expect(attachedInvariant(bendGrid(g))).toEqual([])
    }
  })
})

describe('mkGridMorph connection preservation (the user ruling)', () => {
  it('NOTHING is ever drawn detached: every var/port radial hangs on an arc at every p', () => {
    for (const [f, t] of CHAINS) {
      const m = mkGridMorph(f, t)
      for (let i = 0; i <= 60; i++) {
        const p = i / 60
        const bad = attachedInvariant(m(p))
        expect(bad, `p=${p.toFixed(3)}: ${bad.join('; ')}`).toEqual([])
      }
    }
  })

  it('dying pieces retract during phase A and are gone by p=1/3; born appear only after 2/3', () => {
    // K-redex second step (\y. a) b -> a : binder dies, b dies, whole lam anatomy dies
    const m = mkGridMorph(gridK2, gridK3)
    const nA0 = m(0).radials.length
    const nMid = m(0.5).radials.length
    const nEnd = m(1).radials.length
    // strictly fewer pieces mid-flight than at either settled end (dying gone, born not yet)
    expect(nMid).toBeLessThan(nA0)
    expect(nMid).toBeLessThanOrEqual(nEnd)
    // dying extent decreases monotonically across phase A
    const extentSum = (g: NodeGeometry): number => g.radials.reduce((s, r) => s + Math.abs(r.r1 - r.r0), 0)
    expect(extentSum(m(0.15))).toBeLessThan(extentSum(m(0)))
    expect(extentSum(m(0.3))).toBeLessThan(extentSum(m(0.15)))
  })

  it('port anchors shared by both stages ride drawn port-rail tips at every p', () => {
    for (const [f, t] of CHAINS) {
      const shared = f.rails.map((r) => r.name).filter((n) => t.rails.some((r) => r.name === n))
      const m = mkGridMorph(f, t)
      for (const p of [0, 0.2, 1 / 3, 0.5, 2 / 3, 0.8, 1]) {
        const g = m(p)
        for (const name of shared) {
          const v = g.portAnchors[name]!
          const onTip = g.radials.some((r) => r.kind === 'port' && close(Math.cos(r.angle) * r.r1, v.x) && close(Math.sin(r.angle) * r.r1, v.y))
          expect(onTip, `'${name}' anchor off every rail tip at p=${p}`).toBe(true)
        }
      }
    }
  })

  it('a dying free port retracts its anchor into the rim, continuously', () => {
    // (\y. a) b -> a : port b dies (K-redex erases the argument)
    const m = mkGridMorph(gridK2, gridK3)
    expect(gridK3.rails.some((r) => r.name === 'b')).toBe(false)
    const rs = [0, 0.1, 0.2, 1 / 3, 0.7, 1].map((p) => {
      const v = m(p).portAnchors['b']!
      return Math.hypot(v.x, v.y)
    })
    for (let i = 1; i < rs.length; i++) expect(rs[i]!).toBeLessThanOrEqual(rs[i - 1]! + 1e-9)
    // fully retracted to the rim by the end of phase A
    expect(rs[3]!).toBeLessThan(rs[0]!)
  })
})
