import { beforeAll, describe, expect, it } from 'vitest'
import { buildFregeTheory } from '../../src/theories/frege'
import { verifyTheory } from '../../src/kernel/proof/context'
import { mkReplay, type Replay } from '../../src/app/replay'
import { scene3, type Entity } from '../../src/view3d/scene'
import { diagramSpec } from '../../src/view3d/spec'
import { layoutTree } from '../../src/view3d/layout'
import { cross3, dist3, dot3, norm3, segPointDist, sub3 } from '../../src/view3d/vec3'

/** Proof-scale wire-quality laws, pinned to the zeroIsNat steps where both
    failures were observed (USER report 2026-08-15): a strand that jutted
    9.5 units off its chord at 5.1× chord length (step 22), and one that
    wound 1.31π around the trunk (step 23) — both artifacts of escape steps
    choosing an obstacle's side by accident instead of by path length.
    Thresholds sit strictly between the failing and the shortest-detour
    measurements (ratio 5.14 vs 1.15, deviation 9.54 vs 0.68, winding
    1.31π vs 1.18π). */
describe('zeroIsNat wire quality', () => {
  let replay: Replay
  beforeAll(() => {
    replay = mkReplay('zeroIsNat', verifyTheory(buildFregeTheory()))
  })

  for (const step of [22, 23]) {
    it(`step ${step}: no strand juts, wanders, or spirals`, () => {
      const d = replay.diagramAt(step)
      const s = scene3(d)
      const tl = layoutTree(diagramSpec(d))
      for (const e of s.entities) {
        if (e.kind !== 'strand') continue
        const st = e as Extract<Entity, { kind: 'strand' }>
        const p = st.pts[0]!, q = st.pts[st.pts.length - 1]!
        const chord = Math.max(dist3(p, q), 1e-6)
        let len = 0
        let dev = 0
        for (let i = 1; i < st.pts.length; i++) len += dist3(st.pts[i - 1]!, st.pts[i]!)
        for (const pt of st.pts) dev = Math.max(dev, segPointDist(pt, p, q))
        expect(len / chord, `${st.key} length/chord`).toBeLessThanOrEqual(2.0)
        expect(dev, `${st.key} deviation from chord`).toBeLessThanOrEqual(2.5)
        // Anti-tangle laws (USER report 2026-08-15: the strand at the fan
        // point doubled back on itself, almost a loop — a Steiner junction
        // parked in the congested fan crotch). Pre-fix: sharpest turn dot
        // −0.76 and self-proximity 0.39; post-fix 0.07 and 0.55.
        for (let i = 1; i < st.pts.length - 1; i++) {
          const u = sub3(st.pts[i]!, st.pts[i - 1]!), w = sub3(st.pts[i + 1]!, st.pts[i]!)
          const lu = dist3(st.pts[i]!, st.pts[i - 1]!), lw = dist3(st.pts[i + 1]!, st.pts[i]!)
          if (lu < 1e-9 || lw < 1e-9) continue
          expect(dot3(u, w) / (lu * lw), `${st.key} doubling back at sample ${i}`).toBeGreaterThanOrEqual(-0.3)
        }
        for (let i = 0; i < st.pts.length; i++) for (let j = i + 6; j < st.pts.length; j++) {
          expect(dist3(st.pts[i]!, st.pts[j]!), `${st.key} self-loop between samples ${i},${j}`).toBeGreaterThanOrEqual(0.45)
        }
        for (const pr of tl.regions.values()) {
          const n1 = pr.ref, n2 = norm3(cross3(pr.dir, n1))
          let wind = 0
          let prev: number | null = null
          for (const pt of st.pts) {
            const rel = sub3(pt, pr.base)
            const x = dot3(rel, n1), y = dot3(rel, n2)
            if (Math.hypot(x, y) < 0.2) { prev = null; continue }
            const az = Math.atan2(y, x)
            if (prev !== null) {
              let daz = az - prev
              while (daz > Math.PI) daz -= 2 * Math.PI
              while (daz < -Math.PI) daz += 2 * Math.PI
              wind += daz
            }
            prev = az
          }
          expect(Math.abs(wind), `${st.key} winding about ${pr.region}`).toBeLessThanOrEqual(Math.PI * 1.25)
        }
      }
    })
  }
})
