import { describe, it, expect } from 'vitest'
import { mkEngine } from '../../src/view/engine'
import type { Engine } from '../../src/view/engine'
import {
  recomputeRegions, resolveOverlaps, establishFrame, segSeparationE, wireEnergyCapture, WIREP,
} from '../../src/view/relax'
import type { WireSeg } from '../../src/view/relax'
import { identityJunctionScene, identityRefScene } from '../fixtures/zero-signature'

/**
 * EXACTNESS OF THE SPATIAL-HASH separation (plan Task 8a). `segSeparationE` is now
 * a uniform-grid enumeration; it must equal the naive all-pairs enumeration to
 * float exactness. The all-pairs reference (kernel + loop) is INLINED here — it is
 * the oracle, not kept in src.
 */

/** The exact per-pair kernel (copy of relax.segPairSepE — the oracle). */
function refPairE(A: WireSeg, B: WireSeg, R: number): number {
  if (Math.min(A.a.x, A.b.x) - R > Math.max(B.a.x, B.b.x) || Math.min(B.a.x, B.b.x) - R > Math.max(A.a.x, A.b.x)) return 0
  if (Math.min(A.a.y, A.b.y) - R > Math.max(B.a.y, B.b.y) || Math.min(B.a.y, B.b.y) - R > Math.max(A.a.y, A.b.y)) return 0
  const N = 8
  let E = 0
  for (let ki = 0; ki <= N; ki++) {
    const ta = ki / N
    const pa = { x: A.a.x + (A.b.x - A.a.x) * ta, y: A.a.y + (A.b.y - A.a.y) * ta }
    for (let kj = 0; kj <= N; kj++) {
      const tb = kj / N
      const pb = { x: B.a.x + (B.b.x - B.a.x) * tb, y: B.a.y + (B.b.y - B.a.y) * tb }
      const d = Math.hypot(pa.x - pb.x, pa.y - pb.y)
      if (d < R) E += (WIREP.sepSlope * (R - d) * (R - d)) / R / (N * N)
    }
  }
  return E
}

/** The naive all-pairs reference. */
function refSep(segs: readonly WireSeg[], sc: number): number {
  const R = WIREP.sepR * sc
  let E = 0
  for (let i = 0; i < segs.length; i++) {
    for (let j = i + 1; j < segs.length; j++) {
      if (segs[i]!.wid === segs[j]!.wid) continue
      E += refPairE(segs[i]!, segs[j]!, R)
    }
  }
  return E
}

const close = (a: number, b: number): boolean => Math.abs(a - b) <= 1e-9 * (Math.abs(b) + 1)

function mkRng(seed: number): () => number {
  let s = seed >>> 0
  if (s === 0) s = 0x9e3779b9
  return () => { s ^= s << 13; s >>>= 0; s ^= s >>> 17; s ^= s << 5; s >>>= 0; return s / 4294967296 }
}

function fixtureEngine(name: 'identity-ref' | 'identity-junction'): Engine {
  const diagram = name === 'identity-ref' ? identityRefScene() : identityJunctionScene()
  const e = mkEngine(diagram, [])
  recomputeRegions(e); resolveOverlaps(e); establishFrame(e); recomputeRegions(e)
  return e
}

describe('spatial-hash segSeparationE equals all-pairs (plan Task 8a)', () => {
  it('synthetic random segment clouds — many wires, mixed near/far, at cell-scale', () => {
    const rng = mkRng(0x5e9a)
    const sc = 1
    const R = WIREP.sepR * sc
    for (let trial = 0; trial < 40; trial++) {
      const nWires = 1 + Math.floor(rng() * 6)
      const nSeg = 20 + Math.floor(rng() * 200)
      // spread over a box a few cells wide so near AND far pairs both occur, and
      // some segments straddle cell boundaries and span multiple cells.
      const span = R * (2 + rng() * 6)
      const segs: WireSeg[] = []
      for (let i = 0; i < nSeg; i++) {
        const ax = rng() * span, ay = rng() * span
        const len = rng() * R * 2
        const ang = rng() * 2 * Math.PI
        segs.push({
          wid: `w${Math.floor(rng() * nWires)}`,
          a: { x: ax, y: ay },
          b: { x: ax + Math.cos(ang) * len, y: ay + Math.sin(ang) * len },
        })
      }
      const hashed = segSeparationE(segs, sc)
      const ref = refSep(segs, sc)
      expect(close(hashed, ref), `trial ${trial}: hashed ${hashed} vs ref ${ref}`).toBe(true)
    }
  })

  it('zero-signature fixture states plus 50 seeded perturbations', () => {
    for (const [name, seed] of [
      ['identity-ref', 20],
      ['identity-junction', 48],
    ] as const) {
      const e = fixtureEngine(name)
      const rng = mkRng(0xc0ffee ^ seed)
      for (let variant = 0; variant <= 50; variant++) {
        if (variant > 0) {
          // perturb every body a little, then re-measure
          for (const b of e.bodies.values()) {
            b.pos = { x: b.pos.x + (rng() - 0.5) * 8 * e.scale, y: b.pos.y + (rng() - 0.5) * 8 * e.scale }
          }
          recomputeRegions(e)
        }
        const segs = wireEnergyCapture(e).segs
        const hashed = segSeparationE(segs, e.scale)
        const ref = refSep(segs, e.scale)
        expect(close(hashed, ref), `${name} variant ${variant}: hashed ${hashed} vs ref ${ref} (${segs.length} segs)`).toBe(true)
      }
    }
  })
})
