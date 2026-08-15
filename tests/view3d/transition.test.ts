import { describe, expect, it } from 'vitest'
import { planTransition, resample, sceneAt } from '../../src/view3d/transition'
import type { Scene3 } from '../../src/view3d/scene'
import { dist3, v3 } from '../../src/view3d/vec3'

const sc = (entities: Scene3['entities'], radius = 10): Scene3 => ({ entities, center: v3(0, 0, 0), radius })

describe('planTransition / sceneAt', () => {
  it('matches by key: shared keys move, others enter/exit', () => {
    const prev = sc([
      { kind: 'branch', key: 'b:r0', pts: [v3(0, 0, 0), v3(0, 5, 0)] },
      { kind: 'bead', key: 'd:r1', pos: v3(0, 2, 0) },
    ])
    const next = sc([
      { kind: 'branch', key: 'b:r0', pts: [v3(0, 0, 0), v3(0, 8, 0)] },
      { kind: 'strand', key: 's:w0:0', wire: 'w0', pts: [v3(1, 0, 0), v3(1, 2, 0)] },
    ])
    const plan = planTransition(prev, next)
    expect(plan.moves.map((m) => m.from.key)).toEqual(['b:r0'])
    expect(plan.exits.map((e) => e.key)).toEqual(['d:r1'])
    expect(plan.enters.map((e) => e.key)).toEqual(['s:w0:0'])
  })
  it('t=0 reproduces prev geometry, t=1 next; enters/exits fade', () => {
    const prev = sc([{ kind: 'branch', key: 'b:r0', pts: [v3(0, 0, 0), v3(0, 5, 0)] }])
    const next = sc([
      { kind: 'branch', key: 'b:r0', pts: [v3(0, 0, 0), v3(0, 8, 0)] },
      { kind: 'bead', key: 'd:r1', pos: v3(0, 3, 0) },
    ])
    const plan = planTransition(prev, next)
    const at0 = sceneAt(plan, 0)
    const at1 = sceneAt(plan, 1)
    const branch0 = at0.entities.find((e) => e.key === 'b:r0')!
    const branch1 = at1.entities.find((e) => e.key === 'b:r0')!
    expect('pts' in branch0 && dist3(branch0.pts[branch0.pts.length - 1]!, v3(0, 5, 0))).toBeLessThan(1e-9)
    expect('pts' in branch1 && dist3(branch1.pts[branch1.pts.length - 1]!, v3(0, 8, 0))).toBeLessThan(1e-9)
    const bead0 = at0.entities.find((e) => e.key === 'd:r1')!
    const bead1 = at1.entities.find((e) => e.key === 'd:r1')!
    expect(bead0.alpha).toBe(0)
    expect(bead1.alpha).toBe(1)
  })
  it('bounds interpolate', () => {
    const plan = planTransition(sc([], 4), sc([], 8))
    expect(sceneAt(plan, 0).radius).toBeCloseTo(4, 9)
    expect(sceneAt(plan, 1).radius).toBeCloseTo(8, 9)
  })
  it('throws loudly when a key changes entity shape between scenes', () => {
    const prev = sc([{ kind: 'bead', key: 'd:r1', pos: v3(0, 1, 0) }])
    const next = sc([{ kind: 'branch', key: 'd:r1', pts: [v3(0, 0, 0), v3(0, 2, 0)] }])
    const plan = planTransition(prev, next)
    expect(() => sceneAt(plan, 0.5)).toThrow('changed entity shape')
  })
  it('plans from an interrupted-tween scene (a sceneAt output) without popping', () => {
    // An interrupted tween: while animating prev -> mid, a new target (next)
    // arrives. The correct "from" scene for the new plan is the currently
    // DISPLAYED interpolated scene (sceneAt at the current t), not the
    // original prev — otherwise the entity visibly jumps back to prev's
    // geometry before animating onward.
    const prev = sc([
      { kind: 'branch', key: 'b:r0', pts: [v3(0, 0, 0), v3(0, 5, 0)] },
    ])
    const mid = sc([
      { kind: 'branch', key: 'b:r0', pts: [v3(0, 0, 0), v3(0, 8, 0)] },
      { kind: 'bead', key: 'd:r1', pos: v3(0, 3, 0) },
    ])
    const interrupted = sceneAt(planTransition(prev, mid), 0.5) // mid-tween snapshot
    const next = sc([{ kind: 'branch', key: 'b:r0', pts: [v3(0, 0, 0), v3(0, 2, 0)] }])
    const resumed = planTransition(interrupted, next)
    const move = resumed.moves.find((m) => m.from.key === 'b:r0')!
    const interruptedBranch = interrupted.entities.find((e) => e.key === 'b:r0')!
    expect(
      'pts' in move.from && 'pts' in interruptedBranch
      && dist3(move.from.pts[0]!, interruptedBranch.pts[0]!),
    ).toBeLessThan(1e-9)
    // the bead that was fading in mid-tween now exits from its CURRENT
    // partial-alpha state, not reset to prev's full alpha.
    expect(resumed.exits.map((e) => e.key)).toEqual(['d:r1'])
    const interruptedBead = interrupted.entities.find((e) => e.key === 'd:r1')!
    const exitedBead = resumed.exits[0]! as { alpha?: number }
    expect(exitedBead.alpha).toBeCloseTo(interruptedBead.alpha!, 9)
  })
})

describe('resample', () => {
  it('keeps endpoints exact and spaces uniformly by arc length', () => {
    const pts = [v3(0, 0, 0), v3(1, 0, 0), v3(1, 1, 0)]
    const r = resample(pts, 5)
    expect(r.length).toBe(5)
    expect(dist3(r[0]!, pts[0]!)).toBeLessThan(1e-12)
    expect(dist3(r[4]!, pts[2]!)).toBeLessThan(1e-12)
    expect(dist3(r[2]!, v3(1, 0, 0))).toBeLessThan(1e-9) // midpoint of a 2-length path
  })
})
