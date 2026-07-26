import { describe, it, expect } from 'vitest'
import { mkEngine } from '../../src/view/engine'
import { LayoutOptimizer } from '../../src/view/optimize'
import { identityJunctionScene } from '../fixtures/zero-signature'

/**
 * THE WALK-GATE STRICT-DESCENT CONTRACT (plan Task 8, USER limit-cycle repro).
 *
 * `walkWires`/`advanceNetwork` moves ONE wire's junctions at a time and used to
 * gate acceptance on that wire's ROD length alone — excluding the inter-wire
 * separation term of the total energy. So the walk could trade rod cost down
 * while pushing separation UP without bound: a limit cycle in which `settleStep`
 * returns true forever, the full layoutScore never settles below best−eps, the
 * phase-0 descent never reaches rest, calibration never starts (T pinned at 0),
 * and the app sits at the raw seed indefinitely (observed live 60+ s).
 *
 * The fix gates each wire's substep and split on rod(w) + separation(w vs the
 * OTHER wires' fixed segments) = ΔE_total restricted to w's coordinates — a strict
 * descent of the whole objective, so the cycle is impossible by construction.
 *
 * Repro: drive the LayoutOptimizer on a junction-rich raw seed. Before the
 * fix it never leaves phase-0 descent (T stays 0); after it, the descent reaches
 * rest and the 16-probe calibration completes (T becomes nonzero).
 */

describe('walk gate is a strict descent of the FULL energy (plan Task 8)', () => {
  it('phase-0 descent reaches rest and enters calibration (no rod-vs-separation limit cycle)', () => {
    const e = mkEngine(identityJunctionScene(), [])
    const opt = new LayoutOptimizer(0xace4)
    opt.sync(e, null)
    expect(opt.temperature, 'starts in phase-0 descent').toBe(0)
    const seedScore = opt.best()!.score

    let calibrated = false
    for (let k = 0; k < 400; k++) {
      opt.tick(null, 40)
      if (opt.temperature > 0) { calibrated = true; break }
    }
    // reaching a nonzero temperature means: the descent rested (settleStep returned
    // false) AND all 16 calibration probes ran. A walk-gate limit cycle would spin
    // in phase-0 forever and never get here.
    expect(calibrated, 'phase-0 descent never reached calibration — the walk-gate limit cycle is back').toBe(true)
    // and the descent genuinely improved the raw seed on the way (sanity).
    expect(opt.best()!.score).toBeLessThan(seedScore)
  })
})
