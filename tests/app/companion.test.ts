import { describe, it, expect } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { parseTerm } from '../../src/kernel/term/parse'
import { startSession, applyForward, sideBoundary } from '../../src/app/session'
import type { ProofSession } from '../../src/app/session'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { mkReplay } from '../../src/app/replay'
import type { Replay } from '../../src/app/replay'
import { companionFor } from '../../src/app/companion'
import type { CompanionState } from '../../src/app/companion'
import { bootFixture } from './boot-fixture'

const p = (s: string) => parseTerm(s)

// A toy goal whose two ends are STRUCTURALLY distinct (single node vs. a
// double-cut-wrapped node), so a returned companion diagram identifies which
// side produced it by object identity — not just by shape.
function goalSession(): ProofSession {
  const boot = bootDeferred
  const l = new DiagramBuilder()
  l.termNode(l.root, p('\\x. x'))
  const lhs = mkDiagramWithBoundary(l.build(), [])
  const r = new DiagramBuilder()
  r.termNode(r.root, p('\\x. x'))
  const c1 = r.cut(r.root)
  r.cut(c1)
  const rhs = mkDiagramWithBoundary(r.build(), [])
  return startSession(lhs, rhs, boot.ctx)
}

const bootDeferred = await bootFixture()

// A replay over a bundled theorem: any theorem gives a valid stepper; the
// companion always names the final state regardless of k.
function someReplay(): { replay: Replay; ctx: typeof bootDeferred.ctx } {
  const thm = [...bootDeferred.ctx.theorems.values()][0]
  if (thm === undefined) throw new Error('test setup: no bundled theorems to replay')
  return { replay: mkReplay(thm, bootDeferred.ctx), ctx: bootDeferred.ctx }
}

const st = (over: Partial<CompanionState>): CompanionState => ({
  mode: 'edit', session: null, side: 'forward', replay: null, ...over,
})

describe('companionFor decision table', () => {
  it('EDIT hides the companion regardless of session/side/replay presence', () => {
    expect(companionFor(st({ mode: 'edit' }))).toBeNull()
    const s = goalSession()
    const { replay } = someReplay()
    // even with a live session and a replay object lying around, EDIT is null
    expect(companionFor(st({ mode: 'edit', session: s, replay }))).toBeNull()
    expect(companionFor(st({ mode: 'edit', session: s, side: 'backward', replay }))).toBeNull()
  })

  it('PROVE with no session yet is null (both sides)', () => {
    expect(companionFor(st({ mode: 'prove', session: null, side: 'forward' }))).toBeNull()
    expect(companionFor(st({ mode: 'prove', session: null, side: 'backward' }))).toBeNull()
  })

  it('PROVE·forward shows the BACKWARD side (the meet target) with the rhs boundary', () => {
    const s = goalSession()
    const c = companionFor(st({ mode: 'prove', session: s, side: 'forward' }))
    expect(c).not.toBeNull()
    expect(c!.diagram).toBe(s.backward.current)
    expect(c!.boundary).toBe(sideBoundary(s, 'backward'))
    expect(c!.boundary).toBe(s.rhs.boundary)
    expect(c!.label).toBe('meeting: backward side')
  })

  it('PROVE·backward shows the FORWARD side with the lhs boundary', () => {
    const s = goalSession()
    const c = companionFor(st({ mode: 'prove', session: s, side: 'backward' }))
    expect(c).not.toBeNull()
    expect(c!.diagram).toBe(s.forward.current)
    expect(c!.boundary).toBe(sideBoundary(s, 'forward'))
    expect(c!.boundary).toBe(s.lhs.boundary)
    expect(c!.label).toBe('meeting: forward side')
  })

  it('PROVE·forward on a FRESH session still shows the (unadvanced) backward rhs', () => {
    const s = goalSession()
    expect(s.backward.steps).toHaveLength(0)
    const c = companionFor(st({ mode: 'prove', session: s, side: 'forward' }))
    expect(c!.diagram).toBe(s.backward.current) // the pristine rhs, shown from step 0
  })

  it('PROVE·forward tracks the backward side as it advances (companion follows the live current)', () => {
    let s = goalSession()
    // one forward step on the FORWARD side does not move the backward companion
    const before = companionFor(st({ mode: 'prove', session: s, side: 'forward' }))!.diagram
    s = applyForward(s, {
      rule: 'doubleCutIntro',
      sel: mkSelection(s.forward.current, { region: s.forward.current.root, regions: [], nodes: [], wires: [] }),
    })
    const after = companionFor(st({ mode: 'prove', session: s, side: 'forward' }))!.diagram
    expect(after).toBe(before) // backward.current is untouched by a forward step
    expect(after).toBe(s.backward.current)
  })

  it('REPLAY with no active replay is null', () => {
    expect(companionFor(st({ mode: 'replay', replay: null }))).toBeNull()
  })

  it('REPLAY shows the theorem final state (rhs) with the replay boundary, labelled as the goal', () => {
    const { replay } = someReplay()
    const c = companionFor(st({ mode: 'replay', replay }))
    expect(c).not.toBeNull()
    expect(c!.diagram).toBe(replay.diagramAt(replay.stepCount))
    expect(c!.boundary).toBe(replay.boundary)
    expect(c!.label).toBe('goal: final state')
  })

  it('REPLAY companion is independent of the current step (same final-state object at every k)', () => {
    const { replay } = someReplay()
    const atZero = companionFor(st({ mode: 'replay', replay }))!.diagram
    // stepping the view forward does not change what the companion targets
    const atEnd = companionFor(st({ mode: 'replay', replay }))!.diagram
    expect(atZero).toBe(atEnd)
    // degenerate case: at the last step the displayed diagram IS the companion's
    expect(atEnd).toBe(replay.diagramAt(replay.stepCount))
  })
})
