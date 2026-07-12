import { describe, it, expect } from 'vitest'
import { mkReplay } from '../../src/app/replay'
import { replayActions } from '../../src/kernel/proof/action'
import { exploreForm } from '../../src/kernel/diagram/canonical/explore'
import type { Theorem } from '../../src/kernel/proof/theorem'
import { bootFixture } from './boot-fixture'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../src/kernel/diagram/boundary'

const boot = await bootFixture()
const ctx = boot.ctx
const thm = (name: string): Theorem => {
  const t = ctx.theorems.get(name)
  if (t === undefined) throw new Error(`test setup: no bundled theorem '${name}' (have ${[...ctx.theorems.keys()].join(', ')})`)
  return t
}
// plusComm is the largest bundled derivation — the intended stepping example.
const plusComm = thm('plusComm')

describe('mkReplay', () => {
  it('uses one scrub stop for a genuine multi-step action and exposes every constituent in order', () => {
    const b = new DiagramBuilder()
    const lhs = mkDiagramWithBoundary(b.build(), [])
    const steps = [
      { rule: 'doubleCutIntro' as const, sel: { region: lhs.diagram.root, regions: [], nodes: [], wires: [] } },
      { rule: 'doubleCutElim' as const, region: 'dc' },
    ]
    const action = { label: 'round trip a double cut', steps, placements: [] }
    const theorem: Theorem = { name: 'multi', lhs, rhs: lhs, actions: [action] }
    const replay = mkReplay(theorem, { theorems: new Map(), relations: new Map() })

    expect(replay.actionCount).toBe(1)
    expect(replay.diagramAt(0)).toBe(lhs.diagram)
    expect(exploreForm(replay.diagramAt(1))).toBe(exploreForm(lhs.diagram))
    expect(replay.stepsAt(1)).toEqual(steps)
  })
  it('scrubs by action while exposing the active action constituent steps', () => {
    const r = mkReplay(plusComm, ctx)
    expect(r.actionCount).toBe(plusComm.actions.length)
    expect(r.stepsAt(1)).toBe(plusComm.actions[0]!.steps)
  })
  it('actionCount is the theorem action count', () => {
    const r = mkReplay(plusComm, ctx)
    expect(r.actionCount).toBe(plusComm.actions.length)
    expect(r.actionCount).toBeGreaterThan(0)
  })

  it('step 0 is the left-hand side; the boundary is the lhs boundary', () => {
    const r = mkReplay(plusComm, ctx)
    expect(exploreForm(r.diagramAt(0))).toBe(exploreForm(plusComm.lhs.diagram))
    expect(r.boundary).toBe(plusComm.lhs.boundary)
  })

  it('the last step matches an independently replayed result', () => {
    const r = mkReplay(plusComm, ctx)
    const independent = replayActions(plusComm.lhs.diagram, plusComm.actions, ctx)
    expect(exploreForm(r.diagramAt(r.actionCount))).toBe(exploreForm(independent))
  })

  it('labels are the rule names, 1-based, with the empty string at 0', () => {
    const r = mkReplay(plusComm, ctx)
    expect(r.labelAt(0)).toBe('')
    for (let k = 1; k <= r.actionCount; k++) {
      expect(r.labelAt(k)).toBe(plusComm.actions[k - 1]!.label)
    }
  })

  it('every intermediate matches a fresh prefix replay (correct diagram at each k)', () => {
    const r = mkReplay(plusComm, ctx)
    for (let k = 0; k <= r.actionCount; k++) {
      const fresh = replayActions(plusComm.lhs.diagram, plusComm.actions.slice(0, k), ctx)
      expect(exploreForm(r.diagramAt(k)), `step ${k}`).toBe(exploreForm(fresh))
    }
  })

  it('caches: a monotone walk reuses the cached prefix (same object, not re-replayed)', () => {
    const r = mkReplay(plusComm, ctx)
    // A non-caching stepper returns a fresh diagram object on each call, so the
    // reference at step 3 would NOT survive extending the walk to step 5. The
    // cache keeps the exact object, which object identity observes deterministically.
    const d3a = r.diagramAt(3)
    const d5 = r.diagramAt(5)
    expect(d5).not.toBe(d3a)
    const d3b = r.diagramAt(3)
    expect(d3b).toBe(d3a) // step 3 was not recomputed when the walk advanced to 5
    // And a repeated query never mints a new diagram either.
    expect(r.diagramAt(5)).toBe(d5)
  })

  it('rejects out-of-range steps loudly', () => {
    const r = mkReplay(plusComm, ctx)
    expect(() => r.diagramAt(-1)).toThrow(/out of range/)
    expect(() => r.diagramAt(r.actionCount + 1)).toThrow(/out of range/)
    expect(() => r.diagramAt(1.5)).toThrow(/out of range/)
    expect(() => r.labelAt(-1)).toThrow(/out of range/)
    expect(() => r.labelAt(r.actionCount + 1)).toThrow(/out of range/)
  })
})
