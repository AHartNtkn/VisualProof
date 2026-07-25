import { describe, it, expect } from 'vitest'
import type { Engine } from '../../src/view/engine'
import { mkEngine, subtreeCarriers } from '../../src/view/engine'
import {
  recomputeRegions, resolveOverlaps, establishFrame, wireEnergy, contentEnergy,
} from '../../src/view/relax'
import { mkScoreState, applyMove } from '../../src/view/score-delta'
import { bootFixture } from '../app/boot-fixture'
import { mkReplay } from '../../src/app/replay'
import type { Vec2 } from '../../src/view/vec'

/**
 * THE EXACTNESS CONTRACT for the incremental energy delta (plan Task 3). The
 * tracked total `st.total` maintained by commit()ing a stream of moves must equal
 * a FRESH `wireEnergy(e)+contentEnergy(e)` to float tolerance after every move —
 * the delta evaluator is the acceptance oracle for the local solver's gates and
 * the annealer, so an inexact delta silently changes accept/reject decisions.
 */

const bootCtx = (await bootFixture()).ctx

/** A framed, legal seed (the fixture pattern from frame-budget.test.ts, plus the
    frame so routing bounds and the content frame-wall are exercised). */
function replayEngine(name: string, at: number): Engine {
  const r = mkReplay(name, bootCtx)
  const e = mkEngine(r.diagramAt(at), r.boundaryAt(at))
  recomputeRegions(e)
  resolveOverlaps(e)
  establishFrame(e)
  recomputeRegions(e)
  return e
}

/** Seeded xorshift32 — deterministic, no Math.random (USER LAW). */
function mkRng(seed: number): () => number {
  let s = seed >>> 0
  if (s === 0) s = 0x9e3779b9
  return () => {
    s ^= s << 13; s >>>= 0
    s ^= s >>> 17
    s ^= s << 5; s >>>= 0
    return s / 4294967296
  }
}

const freshTotal = (e: Engine): number => {
  recomputeRegions(e)
  return wireEnergy(e) + contentEnergy(e)
}

type Move = { moved: Set<string>; apply(): void }

/** One random move: 60% single-body displacement, 40% rigid subtree shift. Radius
    in [0.5, 3]·(discR+2)·scale about a random direction (brief spec). */
function randomMove(e: Engine, rng: () => number): Move {
  const ids = [...e.bodies.keys()]
  const regionIds = [...e.membersOf.keys()]
  const disp = (discR: number): Vec2 => {
    const ang = rng() * 2 * Math.PI
    const rad = (0.5 + 2.5 * rng()) * (discR + 2) * e.scale
    return { x: Math.cos(ang) * rad, y: Math.sin(ang) * rad }
  }
  if (rng() < 0.6) {
    const id = ids[Math.floor(rng() * ids.length)]!
    const b = e.bodies.get(id)!
    const d = disp(b.discR)
    return { moved: new Set([id]), apply: () => { b.pos = { x: b.pos.x + d.x, y: b.pos.y + d.y } } }
  }
  const rid = regionIds[Math.floor(rng() * regionIds.length)]!
  const carriers = subtreeCarriers(e, rid)
  const d = disp(5.5)
  return {
    moved: new Set(carriers),
    apply: () => {
      for (const cid of carriers) {
        const b = e.bodies.get(cid)!
        b.pos = { x: b.pos.x + d.x, y: b.pos.y + d.y }
      }
    },
  }
}

describe('incremental energy delta is exact (plan Task 3)', () => {
  for (const [name, at] of [['plusComm', 20], ['succShiftS', 48]] as const) {
    it(`st.total tracks a fresh full eval across 200 random moves — ${name}@${at}`, () => {
      const e = replayEngine(name, at)
      const st = mkScoreState(e)
      // the tracked total starts equal to a fresh eval
      expect(Math.abs(st.total - freshTotal(e))).toBeLessThan(1e-6 * (Math.abs(st.total) + 1))
      const rng = mkRng(0x51ade1 ^ at)
      for (let k = 0; k < 200; k++) {
        const mv = randomMove(e, rng)
        mv.apply()
        recomputeRegions(e)
        const res = applyMove(e, st, mv.moved)
        res.commit()
        if (k % 10 === 9) {
          const fresh = freshTotal(e)
          const tol = 1e-6 * (Math.abs(fresh) + 1)
          expect(Math.abs(st.total - fresh),
            `${name} move ${k}: tracked ${st.total} vs fresh ${fresh} (Δ ${Math.abs(st.total - fresh)})`).toBeLessThan(tol)
        }
      }
    })
  }

  it('abort() after a rejected move leaves st.total at the pre-move eval', () => {
    const e = replayEngine('succShiftS', 48)
    const st = mkScoreState(e)
    const rng = mkRng(0xbead)
    const before = st.total
    for (let k = 0; k < 40; k++) {
      const mv = randomMove(e, rng)
      const saved = new Map([...mv.moved].map((id) => [id, { ...e.bodies.get(id)!.pos }]))
      mv.apply()
      recomputeRegions(e)
      const res = applyMove(e, st, mv.moved)
      // reject: un-mutate the engine, then abort the tentative delta
      for (const [id, p] of saved) e.bodies.get(id)!.pos = p
      recomputeRegions(e)
      res.abort()
    }
    expect(st.total).toBe(before)
    expect(Math.abs(st.total - freshTotal(e))).toBeLessThan(1e-6 * (Math.abs(st.total) + 1))
  })

  // A committed stream of the LARGE random moves (up to 3·(discR+2)·scale) stays
  // exact, and the delta/fresh wall-time ratio is RECORDED (timing is too noisy to
  // gate). On these small, route-dense fixtures the affected set spans most wires
  // (the exact obstacle-reach bound is the inflated disc radius, a large fraction of
  // the layout), so the delta tracks — not dramatically beats — the fresh eval here;
  // its decisive win is on large, lightly route-blocked layouts where a local move
  // leaves the far wires (and the global visibility rebuild) untouched. See
  // .superpowers/sdd/task3-report.md for the full perf analysis.
  it('a committed stream of large moves stays exact; delta/fresh wall-time recorded (succShiftS@48)', () => {
    const e = replayEngine('succShiftS', 48)
    const st = mkScoreState(e)
    const rng = mkRng(0xf00d)

    let deltaMs = 0
    for (let k = 0; k < 200; k++) {
      const mv = randomMove(e, rng)
      mv.apply()
      recomputeRegions(e)
      const t0 = performance.now()
      const res = applyMove(e, st, mv.moved)
      res.commit()
      deltaMs += performance.now() - t0
      if (k % 10 === 9) {
        const fresh = freshTotal(e)
        expect(Math.abs(st.total - fresh), `move ${k}: tracked ${st.total} vs fresh ${fresh}`)
          .toBeLessThan(1e-6 * (Math.abs(fresh) + 1))
      }
    }

    let freshMs = 0
    for (let k = 0; k < 200; k++) {
      const t0 = performance.now()
      recomputeRegions(e)
      wireEnergy(e) + contentEnergy(e)
      freshMs += performance.now() - t0
    }
    console.log(`[score-delta] succShiftS@48 large-move: delta ${deltaMs.toFixed(1)}ms vs fresh ${freshMs.toFixed(1)}ms (ratio ${(deltaMs / freshMs).toFixed(2)})`)
  })
})
