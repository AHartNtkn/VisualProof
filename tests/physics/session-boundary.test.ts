import { describe, expect, it } from 'vitest'
import { buildFregeTheory } from '../../src/theories/frege'
import { verifyTheory } from '../../src/kernel/proof/store'
import { startSession, sideBoundary, currentSide } from '../../src/app/session'
import { mkEngine, settle, frameBounds, frameSlots, computeLegs } from '../../src/view/index'

describe('sideBoundary — prove-mode sides render their statement boundary', () => {
  it('an engine built for a side connects every boundary wire to a fixed frame slot (plan 24)', () => {
    const theory = buildFregeTheory()
    const ctx = verifyTheory(theory)
    const plusComm = theory.theorems.find((t) => t.name === 'plusComm')!
    const s = startSession(plusComm.lhs, plusComm.rhs, ctx)
    const boundary = sideBoundary(s, 'backward')
    expect(boundary.length).toBeGreaterThan(0)
    const e = mkEngine(currentSide(s, 'backward'), boundary)
    settle(e, 1200)
    const slots = frameSlots(frameBounds(e)!, boundary.length)
    const legsByWid = new Map<string, { x: number; y: number }[][]>()
    for (const g of computeLegs(e)) {
      const legs = legsByWid.get(g.leg.wid) ?? []
      legs.push(g.pts)
      legsByWid.set(g.leg.wid, legs)
    }
    boundary.forEach((wid, i) => {
      let best = Infinity
      for (const pts of legsByWid.get(wid)!) {
        for (const end of [pts[0]!, pts[pts.length - 1]!]) {
          best = Math.min(best, Math.hypot(end.x - slots[i]!.point.x, end.y - slots[i]!.point.y))
        }
      }
      expect(best, `boundary ${i} reaches slot ${i}`).toBeLessThan(1.5)
    })
  })
})
