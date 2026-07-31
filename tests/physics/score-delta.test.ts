import { describe, it, expect } from 'vitest'
import type { Engine } from '../../src/view/engine'
import { mkEngine, subtreeCarriers } from '../../src/view/engine'
import {
  recomputeRegions, resolveOverlaps, establishFrame, wireEnergy, contentEnergy,
} from '../../src/view/relax'
import { mkScoreState, applyMove } from '../../src/view/score-delta'
import { mkReplay } from '../../src/app/replay'
import { theoryToJson } from '../../src/kernel/proof/store'
import { buildFregeTheory } from '../../src/theories/frege'
import { emptyLibrary, loadEntry, rebuild } from '../../src/app/library'
import type { Vec2 } from '../../src/view/vec'

/**
 * THE EXACTNESS CONTRACT for the incremental energy delta (annealing redesign
 * D1, resurrected from c7932b8). The tracked total `st.total` maintained by
 * commit()ing a stream of moves must equal a FRESH
 * `wireEnergy(e)+contentEnergy(e)` to float tolerance after every move — the
 * delta evaluator is the acceptance oracle for the local solver's gates and
 * the search chain, so an inexact delta silently changes accept/reject
 * decisions. New coverage vs the original: ROTATION moves (the solver's theta
 * trials) and cut-heavy scenes where a body move drags region circles that are
 * other wires' forbidden routing obstacles (the 2026-07-30 per-wire spaces).
 */

const lib0 = loadEntry(emptyLibrary(), 'frege.json', theoryToJson(buildFregeTheory()))
const ctx = rebuild(lib0).ctx

function replayEngine(name: string, at: number): Engine {
  const r = mkReplay(name, ctx)
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

/** One random move: 45% single-body displacement, 25% rotation, 30% rigid
    subtree shift. Radius in [0.5, 3]·(discR+2)·scale about a random direction. */
function randomMove(e: Engine, rng: () => number): Move {
  const ids = [...e.bodies.keys()]
  const regionIds = [...e.membersOf.keys()]
  const disp = (discR: number): Vec2 => {
    const ang = rng() * 2 * Math.PI
    const rad = (0.5 + 2.5 * rng()) * (discR + 2) * e.scale
    return { x: Math.cos(ang) * rad, y: Math.sin(ang) * rad }
  }
  const pick = rng()
  if (pick < 0.45) {
    const id = ids[Math.floor(rng() * ids.length)]!
    const b = e.bodies.get(id)!
    const d = disp(b.discR)
    return { moved: new Set([id]), apply: () => { b.pos = { x: b.pos.x + d.x, y: b.pos.y + d.y } } }
  }
  if (pick < 0.7) {
    const id = ids[Math.floor(rng() * ids.length)]!
    const b = e.bodies.get(id)!
    const dth = (rng() * 2 - 1) * Math.PI
    return { moved: new Set([id]), apply: () => { b.theta += dth } }
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

describe('incremental energy delta is exact (annealing redesign D1)', () => {
  for (const [name, at] of [['zeroIsNat', 11], ['plusLeftUnit', 39]] as const) {
    it(`st.total tracks a fresh full eval across 200 random moves — ${name}@${at}`, () => {
      const e = replayEngine(name, at)
      const st = mkScoreState(e)
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
    const e = replayEngine('zeroIsNat', 11)
    const st = mkScoreState(e)
    const rng = mkRng(0xbead)
    const before = st.total
    for (let k = 0; k < 40; k++) {
      const mv = randomMove(e, rng)
      const saved = new Map([...mv.moved].map((id) => {
        const b = e.bodies.get(id)!
        return [id, { pos: { ...b.pos }, theta: b.theta }] as const
      }))
      mv.apply()
      recomputeRegions(e)
      const res = applyMove(e, st, mv.moved)
      for (const [id, p] of saved) { const b = e.bodies.get(id)!; b.pos = p.pos; b.theta = p.theta }
      recomputeRegions(e)
      res.abort()
    }
    expect(st.total).toBe(before)
    expect(Math.abs(st.total - freshTotal(e))).toBeLessThan(1e-6 * (Math.abs(st.total) + 1))
  })

  // The delta/fresh wall-time ratio is RECORDED (timing is too noisy to gate).
  it('a committed stream of large moves stays exact; delta/fresh wall-time recorded (oneIsNat@20)', () => {
    const e = replayEngine('oneIsNat', 20)
    const st = mkScoreState(e)
    const rng = mkRng(0xf00d)

    let deltaMs = 0
    for (let k = 0; k < 120; k++) {
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
    for (let k = 0; k < 120; k++) {
      const t0 = performance.now()
      recomputeRegions(e)
      void (wireEnergy(e) + contentEnergy(e))
      freshMs += performance.now() - t0
    }
    console.log(`[score-delta] oneIsNat@20: delta ${deltaMs.toFixed(1)}ms vs fresh ${freshMs.toFixed(1)}ms (ratio ${(deltaMs / freshMs).toFixed(2)})`)
  })
})
