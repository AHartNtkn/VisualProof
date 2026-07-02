import { it, expect } from 'vitest'
import { mkEngine } from '../../src/view/engine'
import { recomputeRegions } from '../../src/view/relax'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { parseTerm } from '../../src/kernel/term/parse'

// deterministic pseudo-random for reproducibility
let seed = 12345
const rnd = () => { seed = (seed * 1103515245 + 12345) & 0x7fffffff; return seed / 0x7fffffff }

it('property: region circles enclose all content tightly and reproducibly', () => {
  const p = (s: string) => parseTerm(s)
  for (let trial = 0; trial < 40; trial++) {
    const h = new DiagramBuilder()
    const n = 2 + Math.floor(rnd() * 8)
    const ids = []
    for (let i = 0; i < n; i++) ids.push(h.termNode(h.root, p('\\x. x')))
    const e = mkEngine(h.build(), [])
    for (const id of ids) {
      const b = e.bodies.get(id)!
      b.pos = { x: (rnd() - 0.5) * 800, y: (rnd() - 0.5) * 800 }
    }
    recomputeRegions(e)
    const g1 = e.regions.get(e.d.root)!
    // encloses every disc
    for (const id of ids) {
      const b = e.bodies.get(id)!
      expect(Math.hypot(b.pos.x - g1.center.x, b.pos.y - g1.center.y) + b.discR).toBeLessThanOrEqual(g1.radius + 1e-6)
    }
    // reproducible: identical inputs give the identical circle (no wobble)
    recomputeRegions(e)
    const g2 = e.regions.get(e.d.root)!
    expect(g2.center.x).toBe(g1.center.x)
    expect(g2.center.y).toBe(g1.center.y)
    expect(g2.radius).toBe(g1.radius)
    // near-minimal: some disc touches the rim within a tight tolerance
    let maxReach = 0
    for (const id of ids) {
      const b = e.bodies.get(id)!
      maxReach = Math.max(maxReach, Math.hypot(b.pos.x - g1.center.x, b.pos.y - g1.center.y) + b.discR)
    }
    expect(g1.radius - 5 - maxReach, `trial ${trial}: slack ${(g1.radius - 5 - maxReach).toFixed(3)}`).toBeLessThanOrEqual(0.25)
  }
})
