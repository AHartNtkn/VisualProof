import { describe, expect, it } from 'vitest'
import {
  planTransition,
  resample,
  SCENE_TWEEN_MS,
  SceneTweenTrack,
  sceneAt,
} from '../../src/view3d/transition'
import type { Scene3 } from '../../src/view3d/scene'
import { dist3, v3 } from '../../src/view3d/vec3'

const sc = (entities: Scene3['entities'], radius = 10): Scene3 => ({ entities, center: v3(0, 0, 0), radius })

describe('planTransition / sceneAt', () => {
  it('matches by key: shared keys move, others enter/exit', () => {
    const prev = sc([
      { kind: 'branch', key: 'b:r0', region: 'r0', polarity: 0, pts: [v3(0, 0, 0), v3(0, 5, 0)] },
      { kind: 'pip', key: 'p:n1', node: 'n1', ownerWire: null, pos: v3(0, 2, 0) },
    ])
    const next = sc([
      { kind: 'branch', key: 'b:r0', region: 'r0', polarity: 0, pts: [v3(0, 0, 0), v3(0, 8, 0)] },
      { kind: 'strand', key: 's:w0:0', wire: 'w0', pts: [v3(1, 0, 0), v3(1, 2, 0)] },
    ])
    const plan = planTransition(prev, next)
    expect(plan.moves.map((m) => m.from.key)).toEqual(['b:r0'])
    expect(plan.exits.map((e) => e.key)).toEqual(['p:n1'])
    expect(plan.enters.map((e) => e.key)).toEqual(['s:w0:0'])
  })
  it('t=0 reproduces prev geometry, t=1 next; enters/exits fade', () => {
    const prev = sc([{ kind: 'branch', key: 'b:r0', region: 'r0', polarity: 0, pts: [v3(0, 0, 0), v3(0, 5, 0)] }])
    const next = sc([
      { kind: 'branch', key: 'b:r0', region: 'r0', polarity: 0, pts: [v3(0, 0, 0), v3(0, 8, 0)] },
      { kind: 'pip', key: 'p:n1', node: 'n1', ownerWire: null, pos: v3(0, 3, 0) },
    ])
    const plan = planTransition(prev, next)
    const at0 = sceneAt(plan, 0)
    const at1 = sceneAt(plan, 1)
    const branch0 = at0.entities.find((e) => e.key === 'b:r0')!
    const branch1 = at1.entities.find((e) => e.key === 'b:r0')!
    expect('pts' in branch0 && dist3(branch0.pts[branch0.pts.length - 1]!, v3(0, 5, 0))).toBeLessThan(1e-9)
    expect('pts' in branch1 && dist3(branch1.pts[branch1.pts.length - 1]!, v3(0, 8, 0))).toBeLessThan(1e-9)
    const bead0 = at0.entities.find((e) => e.key === 'p:n1')!
    const bead1 = at1.entities.find((e) => e.key === 'p:n1')!
    expect(bead0.alpha).toBe(0)
    expect(bead1.alpha).toBe(1)
  })
  it('bounds interpolate', () => {
    const plan = planTransition(sc([], 4), sc([], 8))
    expect(sceneAt(plan, 0).radius).toBeCloseTo(4, 9)
    expect(sceneAt(plan, 1).radius).toBeCloseTo(8, 9)
  })
  it('throws loudly when a key changes entity shape between scenes', () => {
    const prev = sc([{ kind: 'pip', key: 'p:n1', node: 'n1', ownerWire: null, pos: v3(0, 1, 0) }])
    const next = sc([{ kind: 'branch', key: 'p:n1', region: 'r0', polarity: 0, pts: [v3(0, 0, 0), v3(0, 2, 0)] }])
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
      { kind: 'branch', key: 'b:r0', region: 'r0', polarity: 0, pts: [v3(0, 0, 0), v3(0, 5, 0)] },
    ])
    const mid = sc([
      { kind: 'branch', key: 'b:r0', region: 'r0', polarity: 0, pts: [v3(0, 0, 0), v3(0, 8, 0)] },
      { kind: 'pip', key: 'p:n1', node: 'n1', ownerWire: null, pos: v3(0, 3, 0) },
    ])
    const interrupted = sceneAt(planTransition(prev, mid), 0.5) // mid-tween snapshot
    const next = sc([{ kind: 'branch', key: 'b:r0', region: 'r0', polarity: 0, pts: [v3(0, 0, 0), v3(0, 2, 0)] }])
    const resumed = planTransition(interrupted, next)
    const move = resumed.moves.find((m) => m.from.key === 'b:r0')!
    const interruptedBranch = interrupted.entities.find((e) => e.key === 'b:r0')!
    expect(
      'pts' in move.from && 'pts' in interruptedBranch
      && dist3(move.from.pts[0]!, interruptedBranch.pts[0]!),
    ).toBeLessThan(1e-9)
    // the bead that was fading in mid-tween now exits from its CURRENT
    // partial-alpha state, not reset to prev's full alpha.
    expect(resumed.exits.map((e) => e.key)).toEqual(['p:n1'])
    const interruptedBead = interrupted.entities.find((e) => e.key === 'p:n1')!
    const exitedBead = resumed.exits[0]! as { alpha?: number }
    expect(exitedBead.alpha).toBeCloseTo(interruptedBead.alpha!, 9)
  })
})

describe('SceneTweenTrack', () => {
  it('restarts from the displayed frame without popping and completes on the new target', () => {
    const first = sc([
      { kind: 'branch', key: 'b:r0', region: 'r0', polarity: 0, pts: [v3(0, 0, 0), v3(0, 2, 0)] },
    ])
    const second = sc([
      { kind: 'branch', key: 'b:r0', region: 'r0', polarity: 0, pts: [v3(0, 0, 0), v3(0, 6, 0)] },
    ])
    const third = sc([
      { kind: 'branch', key: 'b:r0', region: 'r0', polarity: 0, pts: [v3(0, 0, 0), v3(0, 10, 0)] },
    ])

    const track = new SceneTweenTrack(first, second, 0)
    const displayed = track.sample(SCENE_TWEEN_MS / 2)
    track.begin(displayed, third, SCENE_TWEEN_MS / 2)

    expect(track.sample(SCENE_TWEEN_MS / 2)).toEqual(displayed)
    expect(track.completed(SCENE_TWEEN_MS * 1.5)).toBe(true)
    expect(track.sample(SCENE_TWEEN_MS * 1.5)).toEqual(third)
    expect(track.target).toBe(third)
  })
})

describe('wire-level strand morphing', () => {
  it('a persisting wire MORPHS from its old geometry — no strand fades, no index pairing', () => {
    // A proof step reshuffles a wire's edge decomposition, so pairing
    // strands by edge index lerps unrelated segments while the rest fade —
    // the "wires split apart and reassemble" chaos (USER report
    // 2026-08-15). The wire is the persistent object: every NEW strand
    // must start ON the old wire's geometry and deform outward, and a
    // persisting wire contributes no enters or exits at all.
    const prev = sc([
      { kind: 'strand', key: 's:w0:0', wire: 'w0', pts: [v3(0, 0, 0), v3(1, 0, 0), v3(2, 0, 0)] },
      { kind: 'strand', key: 's:w0:1', wire: 'w0', pts: [v3(2, 0, 0), v3(3, 0, 0)] },
    ])
    // Next state: same wire, DIFFERENT decomposition (3 strands, new
    // indices, geometry shifted up by 1).
    const next = sc([
      { kind: 'strand', key: 's:w0:0', wire: 'w0', pts: [v3(0, 1, 0), v3(1, 1, 0)] },
      { kind: 'strand', key: 's:w0:1', wire: 'w0', pts: [v3(1, 1, 0), v3(2, 1, 0)] },
      { kind: 'strand', key: 's:w0:2', wire: 'w0', pts: [v3(2, 1, 0), v3(3, 1, 0)] },
    ])
    const plan = planTransition(prev, next)
    expect(plan.enters.filter((e) => e.kind === 'strand').length).toBe(0)
    expect(plan.exits.filter((e) => e.kind === 'strand').length).toBe(0)
    // At t=0 every rendered strand sample lies ON the old wire's geometry
    // (the y=0 polyline chain), so the start frame reads as the old shape.
    const at0 = sceneAt(plan, 0)
    for (const e of at0.entities) {
      if (e.kind !== 'strand') continue
      for (const p of e.pts) {
        expect(Math.abs(p.y)).toBeLessThan(1e-9)
        expect(p.x).toBeGreaterThanOrEqual(-1e-9)
        expect(p.x).toBeLessThanOrEqual(3 + 1e-9)
      }
    }
    // At t=1 the exact next geometry is rendered.
    const at1 = sceneAt(plan, 1)
    const s2 = at1.entities.find((e) => e.key === 's:w0:2')!
    expect('pts' in s2 && dist3(s2.pts[s2.pts.length - 1]!, v3(3, 1, 0))).toBeLessThan(1e-9)
  })
  it('strand fades happen only when the WIRE appears or disappears', () => {
    const prev = sc([{ kind: 'strand', key: 's:wOld:0', wire: 'wOld', pts: [v3(0, 0, 0), v3(1, 0, 0)] }])
    const next = sc([{ kind: 'strand', key: 's:wNew:0', wire: 'wNew', pts: [v3(0, 2, 0), v3(1, 2, 0)] }])
    const plan = planTransition(prev, next)
    expect(plan.exits.map((e) => e.key)).toEqual(['s:wOld:0'])
    expect(plan.enters.map((e) => e.key)).toEqual(['s:wNew:0'])
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
