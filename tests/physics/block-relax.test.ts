import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { relSig, IOTA } from '../../src/kernel/diagram/sig'
import { mkEngine } from '../../src/view/engine'
import { recomputeRegions, seedProject, settleStep } from '../../src/view/relax'

/**
 * BLOCK-LOCAL RELAXATION (annealing redesign D2). The searcher relaxes a hop
 * with everything outside the block TOTALLY frozen, so the measured defect —
 * a hop's global relaxation moving bodies the move never touched as far as
 * the ones it did (median 5.81 vs 5.53 wu, 2026-07-28) — is impossible by
 * construction. The contract pinned here: `settleStep(e, pinned, frozen)`
 * never changes a frozen body's pose (position OR rotation — the freeze is
 * total, unlike the user drag's position-only pin), and never moves the
 * junctions of a wire whose every terminal is frozen.
 */

const UNARY = relSig([IOTA])

describe('the searcher freeze mask confines relaxation to the block', () => {
  it('frozen bodies and fully-frozen wires are bit-immobile; the block settles', () => {
    const b = new DiagramBuilder()
    const refs = ['A', 'B', 'C', 'D', 'E', 'F'].map((n) => b.ref(b.root, n, UNARY))
    // a 3-terminal wire among the first three (its junction is walkable state)
    b.wire(b.root, refs.slice(0, 3).map((node) => ({ node, port: { kind: 'arg' as const, index: 0 } })))
    // a 3-terminal wire among the last three
    b.wire(b.root, refs.slice(3).map((node) => ({ node, port: { kind: 'arg' as const, index: 0 } })))
    const e = mkEngine(b.build(), [])
    seedProject(e)

    // perturb EVERYTHING off rest so both halves would move if free
    let k = 0
    for (const body of e.bodies.values()) {
      body.pos = { x: body.pos.x + Math.cos(k * 2.1) * 9, y: body.pos.y + Math.sin(k * 2.1) * 9 }
      body.theta += 0.7
      k++
    }
    recomputeRegions(e)

    // block = the first wire's three refs (plus their dots stay frozen — the
    // block is exactly what the caller names)
    const block = new Set(refs.slice(0, 3))
    const frozen = new Set<string>()
    for (const id of e.bodies.keys()) if (!block.has(id)) frozen.add(id)

    const frozenPose = new Map([...e.bodies].filter(([id]) => frozen.has(id))
      .map(([id, body]) => [id, { pos: { ...body.pos }, theta: body.theta }]))
    const frozenWireNets = new Map([...e.wires]
      .filter(([, w]) => w.binds.every((bd) => frozen.has(bd.body)) && (w.endBodyId === null || frozen.has(w.endBodyId)))
      .map(([wid, w]) => [wid, JSON.stringify(w.net)]))
    expect(frozenWireNets.size, 'sanity: the fixture has a fully-frozen wire').toBeGreaterThan(0)

    let blockMoved = 0
    const before = new Map([...e.bodies].map(([id, body]) => [id, { ...body.pos }]))
    for (let t = 0; t < 120; t++) if (!settleStep(e, null, frozen)) break
    for (const id of block) {
      const p0 = before.get(id)!, p1 = e.bodies.get(id)!.pos
      blockMoved = Math.max(blockMoved, Math.hypot(p1.x - p0.x, p1.y - p0.y))
    }

    expect(blockMoved, 'sanity: the block actually settles (bodies move)').toBeGreaterThan(0.5)
    for (const [id, saved] of frozenPose) {
      const body = e.bodies.get(id)!
      expect(body.pos.x, `frozen body ${id} moved in x`).toBe(saved.pos.x)
      expect(body.pos.y, `frozen body ${id} moved in y`).toBe(saved.pos.y)
      expect(body.theta, `frozen body ${id} rotated`).toBe(saved.theta)
    }
    for (const [wid, net] of frozenWireNets) {
      expect(JSON.stringify(e.wires.get(wid)!.net), `fully-frozen wire ${wid}'s net changed`).toBe(net)
    }
  })
})
