import { describe, it, expect } from 'vitest'
import { mkEngine } from '../../src/view/engine'
import type { Engine } from '../../src/view/engine'
import {
  recomputeRegions, resolveOverlaps, establishFrame, wireEnergyCapture, frozenWireEnergy,
  mkFrozenState, frozenProbe,
} from '../../src/view/relax'
import { bootFixture } from '../app/boot-fixture'
import { mkReplay } from '../../src/app/replay'

/**
 * EXACTNESS OF THE FROZEN-PROBE DELTA (plan Task 8b). `frozenProbe(fst, e, body)`
 * must equal a FRESH `frozenWireEnergy(displaced) − frozenWireEnergy(base)` for a
 * probe that displaces any single coordinate of any single body — this is the
 * envelope-probe evaluator the gradient loop runs ~114× per step, so an inexact
 * delta would silently change the descent direction.
 */

const bootCtx = (await bootFixture()).ctx

const close = (a: number, b: number): boolean => Math.abs(a - b) <= 1e-9 * (Math.abs(b) + 1)

function mkRng(seed: number): () => number {
  let s = seed >>> 0
  if (s === 0) s = 0x9e3779b9
  return () => { s ^= s << 13; s >>>= 0; s ^= s >>> 17; s ^= s << 5; s >>>= 0; return s / 4294967296 }
}

function replayEngine(name: string, at: number): Engine {
  const r = mkReplay(name, bootCtx)
  const e = mkEngine(r.diagramAt(at), r.boundaryAt(at))
  recomputeRegions(e); resolveOverlaps(e); establishFrame(e); recomputeRegions(e)
  return e
}

describe('frozen-probe delta equals a fresh frozen eval (plan Task 8b)', () => {
  for (const [name, at] of [['plusComm', 20], ['succShiftS', 48]] as const) {
    it(`every body × {x,y,θ}, seeded displacements — ${name}@${at}`, () => {
      const e = replayEngine(name, at)
      const rng = mkRng(0xf1_02_be ^ at)
      const sc = e.scale
      for (let variant = 0; variant < 4; variant++) {
        if (variant > 0) {
          for (const b of e.bodies.values()) {
            b.pos = { x: b.pos.x + (rng() - 0.5) * 10 * sc, y: b.pos.y + (rng() - 0.5) * 10 * sc }
            b.theta += (rng() - 0.5) * 1.5
          }
          recomputeRegions(e)
        }
        const capBase = wireEnergyCapture(e)
        const fst = mkFrozenState(e)
        const frozenBase = frozenWireEnergy(e, capBase.edges)
        // the frozen state's cached total must equal a fresh frozen eval at base
        expect(close(fst.frozenTotal, frozenBase), `${name} v${variant}: fst.frozenTotal ${fst.frozenTotal} vs fresh ${frozenBase}`).toBe(true)

        for (const b of [...e.bodies.values()]) {
          const setters: [string, () => void, () => void][] = [
            ['x', () => { b.pos = { x: b.pos.x + (rng() - 0.5) * 6 * sc, y: b.pos.y } }, () => {}],
            ['y', () => { b.pos = { x: b.pos.x, y: b.pos.y + (rng() - 0.5) * 6 * sc } }, () => {}],
            ['θ', () => { b.theta += (rng() - 0.5) * 2 }, () => {}],
          ]
          for (const [coord, mutate] of setters) {
            const savedPos = { ...b.pos }, savedTheta = b.theta
            mutate()
            recomputeRegions(e)
            const refDelta = frozenWireEnergy(e, capBase.edges) - frozenBase
            const probeDelta = frozenProbe(fst, e, b.id)
            expect(close(probeDelta, refDelta),
              `${name} v${variant} body ${b.id} d${coord}: probe ${probeDelta} vs fresh ${refDelta} (Δ ${Math.abs(probeDelta - refDelta).toExponential(2)})`).toBe(true)
            b.pos = savedPos; b.theta = savedTheta
          }
        }
        recomputeRegions(e)
      }
    })
  }
})
