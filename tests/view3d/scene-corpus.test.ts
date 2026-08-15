import { describe, expect, it } from 'vitest'
import { GENERATOR_FAMILIES, readKnobs } from '../../src/generate/index'
import { seededRng } from '../../src/generate/rng'
import { scene3 } from '../../src/view3d/scene'

/** The whole pipeline over generator-family diagrams — the guard the
    per-module fixtures cannot provide, because routing failures live at the
    seams (congested fan points, near-anchor exemption boundaries) that only
    realistic diagrams produce. Seeds 1–8 include every prop-shrink seed
    that reproduced the 2026-08-15 routing regressions (exempt-pinned
    samples, point-guarded smoothing limit cycle, single-capsule ping-pong). */
describe('scene3 over generated diagrams', () => {
  for (const family of GENERATOR_FAMILIES) {
    it(`family ${family.id}: seeds 1-8 compose without a routing failure`, () => {
      for (let seed = 1; seed <= 8; seed++) {
        const problem = family.generate(readKnobs(family, {}), seededRng(seed))
        const scene = scene3(problem.diagram)
        expect(scene.entities.length).toBeGreaterThan(0)
        expect(Number.isFinite(scene.radius)).toBe(true)
      }
    })
  }
})
