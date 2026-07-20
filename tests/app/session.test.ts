import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { applyConversion } from '../../src/kernel/rules/conversion'
import { applyClosedTermIntro } from '../../src/kernel/rules/intro'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { buildFregeTheory } from '../../src/theories/frege'
import { verifyTheory } from '../../src/kernel/proof/store'
import { termEq } from '../../src/kernel/term/term'
import { bootFixture } from './boot-fixture'
import {
  startSession, applyForward as applyForwardAction, applyBackward as applyBackwardAction, undoForward, undoBackward, meet, assembleTheorem, sideBoundary, currentSide,
  startTrack, applyTrack as applyTrackAction, undoTrack, redoTrack, declareTrack, trackBoundary, currentTrack, timelineActiveActions,
} from '../../src/app/session'
import type { ProofSession, TrackSession } from '../../src/app/session'
import type { ProofStep } from '../../src/kernel/proof/step'
import { applyAction, singleStepAction, type ProofAction } from '../../src/kernel/proof/action'
import { checkTheorem } from '../../src/kernel/proof/theorem'
import { findDeiterationEvidence } from '../../src/kernel/rules/iteration'

const p = (s: string) => parseTerm(s)
const gesture = (step: ProofStep): ProofAction => singleStepAction(step.rule, step)
const applyTrack = (track: TrackSession, step: ProofStep): TrackSession => applyTrackAction(track, gesture(step))
const applyForward = (session: ProofSession, step: ProofStep): ProofSession => applyForwardAction(session, gesture(step))
const applyBackward = (session: ProofSession, step: ProofStep): ProofSession => applyBackwardAction(session, gesture(step))
const certifiedDeiterationStep = (
  diagram: Parameters<typeof findDeiterationEvidence>[0],
  sel: Parameters<typeof findDeiterationEvidence>[1],
  fuel: number,
): ProofStep => ({ rule: 'deiteration', sel, ...findDeiterationEvidence(diagram, sel, fuel) })
// pure λ fixtures for the citation demos (no term constants)
const YF = p('(\\g. (\\x. g (x x)) (\\x. g (x x))) f')
const FYF = p('s0 ((\\g. (\\x. g (x x)) (\\x. g (x x))) s0)')
const TWOc = p('\\f. \\x. f (f x)')
const ZEROc = p('\\f. \\x. x')

describe('single-track proving', () => {
  it('transports anchored contraction boundaries at root and rejects cut-shielded coalescence', () => {
    const fixture = (shielded: boolean) => {
      const b = new DiagramBuilder()
      const cut = b.cut(b.root)
      const redundant = b.termNode(b.root, p('\\x. x'))
      const survivor = b.termNode(shielded ? cut : b.root, p('\\x. x'))
      const drop = b.wire(b.root, [{ node: redundant, port: { kind: 'output' } }])
      const keep = b.wire(b.root, [{ node: survivor, port: { kind: 'output' } }])
      const step: ProofStep = {
        rule: 'anchoredWireContract',
        redundant,
        survivor,
        certificate: { leftSteps: [], rightSteps: [] },
      }
      return { side: mkDiagramWithBoundary(b.build(), [drop, drop, keep]), drop, keep, step }
    }
    const empty = { theorems: new Map(), relations: new Map() }

    const root = fixture(false)
    const start = startTrack(root.side, 'forward', empty)
    const contracted = applyTrack(start, root.step)
    expect(trackBoundary(contracted)).toEqual([root.keep, root.keep, root.keep])
    expect(trackBoundary(undoTrack(contracted))).toEqual([root.drop, root.drop, root.keep])
    expect(trackBoundary(redoTrack(undoTrack(contracted))))
      .toEqual([root.keep, root.keep, root.keep])
    expect(() => declareTrack(contracted, 'root-coalescence')).not.toThrow()

    const shielded = fixture(true)
    const blocked = startTrack(shielded.side, 'forward', empty)
    expect(() => applyTrack(blocked, shielded.step))
      .toThrowError(new RegExp(`boundary wire '${shielded.drop}' no semantic image`))
    expect(trackBoundary(blocked)).toEqual([shielded.drop, shielded.drop, shielded.keep])
    expect(timelineActiveActions(blocked.timeline)).toEqual([])
  })

  it('treats every multi-step gesture as one history position and one undo/redo', () => {
    const ctx = verifyTheory(buildFregeTheory())
    const b = new DiagramBuilder()
    b.termNode(b.root, p('\\x. x'))
    const origin = mkDiagramWithBoundary(b.build(), [])
    const s0 = startTrack(origin, 'forward', ctx)
    const first = { rule: 'doubleCutIntro' as const, sel: mkSelection(currentTrack(s0), { region: currentTrack(s0).root, regions: [], nodes: [], wires: [] }) }
    const action: ProofAction = { label: 'two gestures inside one action', steps: [first, first], placements: [] }
    const s1 = applyTrackAction(s0, action)
    expect(s1.timeline.states).toHaveLength(2)
    expect(timelineActiveActions(s1.timeline)).toEqual([action])
    expect(undoTrack(s1).timeline.cursor).toBe(0)
    expect(redoTrack(undoTrack(s1)).timeline.cursor).toBe(1)
  })
  it('proves forward from the current diagram, undoes, and declares a checked theorem', () => {
    const ctx = verifyTheory(buildFregeTheory())
    const b = new DiagramBuilder()
    b.termNode(b.root, p('\\x. x'))
    const origin = mkDiagramWithBoundary(b.build(), [])
    const s0 = startTrack(origin, 'forward', ctx)
    const step = {
      rule: 'doubleCutIntro' as const,
      sel: mkSelection(currentTrack(s0), { region: currentTrack(s0).root, regions: [], nodes: [], wires: [] }),
    }
    const s1 = applyTrack(s0, step)
    expect(s1.direction).toBe('forward')
    expect(timelineActiveActions(s1.timeline)).toEqual([gesture(step)])
    expect(currentTrack(undoTrack(s1))).toBe(currentTrack(s0))
    const theorem = declareTrack(s1, 'forwardTrack')
    expect(theorem.lhs).toBe(origin)
    expect(theorem.rhs.diagram).toBe(currentTrack(s1))
    expect(theorem.actions).toEqual([gesture(step)])
    expect(() => checkTheorem(theorem, ctx)).not.toThrow()
  })

  it('proves backward from the current diagram and declares current-to-origin', () => {
    const ctx = verifyTheory(buildFregeTheory())
    const b = new DiagramBuilder()
    b.termNode(b.root, p('\\x. x'))
    const outer = b.cut(b.root)
    b.cut(outer)
    const origin = mkDiagramWithBoundary(b.build(), [])
    const s0 = startTrack(origin, 'backward', ctx)
    const step = { rule: 'doubleCutElim' as const, region: outer }
    const s1 = applyTrack(s0, step)
    expect(s1.direction).toBe('backward')
    const theorem = declareTrack(s1, 'backwardTrack')
    expect(theorem.lhs.diagram).toBe(currentTrack(s1))
    expect(theorem.rhs).toBe(origin)
    expect(theorem.actions).toEqual([])
    expect(theorem.backActions).toEqual([gesture(step)])
    expect(() => checkTheorem(theorem, ctx)).not.toThrow()
  })

  it('retains only origin boundary wires that survive the track', () => {
    const ctx = verifyTheory(buildFregeTheory())
    const b = new DiagramBuilder()
    const node = b.termNode(b.root, p('x'))
    const boundary = b.wire(b.root, [{ node, port: { kind: 'freeVar', name: 'x' } }])
    const origin = mkDiagramWithBoundary(b.build(), [boundary])
    expect(trackBoundary(startTrack(origin, 'backward', ctx))).toEqual([boundary])
  })
})

function goalPair() {
  // goal: an identity node ⟹ the same node double-cut-wrapped (a toy goal)
  const l = new DiagramBuilder()
  const n = l.termNode(l.root, p('\\x. x'))
  const lhsD = l.build()
  const lhs = mkDiagramWithBoundary(lhsD, [])
  const r = new DiagramBuilder()
  const m = r.termNode(r.root, p('\\x. x'))
  const c1 = r.cut(r.root)
  r.cut(c1)
  void m
  const rhs = mkDiagramWithBoundary(r.build(), [])
  return { lhs, rhs, n }
}

describe('proof session', () => {
  it('starts at the goal ends and applies forward steps through the kernel', () => {
    const theory = buildFregeTheory()
    const ctx = verifyTheory(theory)
    const { lhs, rhs } = goalPair()
    const s0 = startSession(lhs, rhs, ctx)
    expect(timelineActiveActions(s0.forward)).toHaveLength(0)
    const s1 = applyForward(s0, {
      rule: 'doubleCutIntro',
      sel: mkSelection(currentSide(s0, 'forward'), { region: currentSide(s0, 'forward').root, regions: [], nodes: [], wires: [] }),
    })
    expect(timelineActiveActions(s1.forward)).toHaveLength(1)
    expect(Object.keys(currentSide(s1, 'forward').regions).length).toBe(3)
  })

  it('meets when forward reaches the rhs and assembles a checkable theorem', () => {
    const theory = buildFregeTheory()
    const ctx = verifyTheory(theory)
    const { lhs, rhs } = goalPair()
    let s = startSession(lhs, rhs, ctx)
    expect(meet(s)).toBe(false)
    s = applyForward(s, {
      rule: 'doubleCutIntro',
      sel: mkSelection(currentSide(s, 'forward'), { region: currentSide(s, 'forward').root, regions: [], nodes: [], wires: [] }),
    })
    expect(meet(s)).toBe(true)
    const thm = assembleTheorem(s, 'toy')
    expect(thm.actions.length).toBeGreaterThan(0)
    expect(thm.name).toBe('toy')
  })

  it('forward refusals surface the kernel message and leave the session unchanged', () => {
    const theory = buildFregeTheory()
    const ctx = verifyTheory(theory)
    const { lhs, rhs, n } = goalPair()
    const s0 = startSession(lhs, rhs, ctx)
    expect(() => applyForward(s0, {
      rule: 'openTermSpawn',
      region: currentSide(s0, 'forward').root,
      term: p('x'),
    })).toThrowError(/spawning requires a negative region/)
    expect(timelineActiveActions(s0.forward)).toHaveLength(0)
    void n
  })

  it('transports a preserved statement boundary through local alias materialization', () => {
    const bodyBuilder = new DiagramBuilder()
    const bodyNode = bodyBuilder.termNode(bodyBuilder.root, p('y'))
    const shared = bodyBuilder.wire(bodyBuilder.root, [{ node: bodyNode, port: { kind: 'output' } }])
    const aliasBody = mkDiagramWithBoundary(bodyBuilder.build(), [shared, shared])

    const host = new DiagramBuilder()
    const ref = host.ref(host.root, 'Alias', 2)
    const c0 = host.termNode(host.root, p('a'))
    const c1 = host.termNode(host.root, p('b'))
    const w0 = host.wire(host.root, [
      { node: ref, port: { kind: 'arg', index: 0 } },
      { node: c0, port: { kind: 'freeVar', name: 'a' } },
    ])
    const w1 = host.wire(host.root, [
      { node: ref, port: { kind: 'arg', index: 1 } },
      { node: c1, port: { kind: 'freeVar', name: 'b' } },
    ])
    const side = mkDiagramWithBoundary(host.build(), [w1])
    const ctx = { theorems: new Map(), relations: new Map([['Alias', aliasBody]]) }
    const session = startSession(side, side, ctx)

    const forward = applyForward(session, { rule: 'relUnfold', node: ref })
    const backward = applyBackward(session, { rule: 'relUnfold', node: ref })
    expect(sideBoundary(forward, 'forward')).toEqual([w1])
    expect(sideBoundary(backward, 'backward')).toEqual([w1])
    expect(currentSide(forward, 'forward').wires[w0]).toBeDefined()
    expect(currentSide(forward, 'forward').wires[w1]).toBeDefined()
    expect(currentSide(backward, 'backward').wires[w0]).toBeDefined()
    expect(currentSide(backward, 'backward').wires[w1]).toBeDefined()
    expect(timelineActiveActions(forward.forward)).toHaveLength(1)
    expect(timelineActiveActions(backward.backward)).toHaveLength(1)
    expect(currentSide(session, 'forward').wires[w0]).toBeDefined()
    expect(currentSide(session, 'forward').wires[w1]).toBeDefined()
    expect(timelineActiveActions(session.forward)).toHaveLength(0)
  })

  it('rejects a multi-step action when an intermediate destroys a fixed boundary even if the final step remints its id', () => {
    const b = new DiagramBuilder()
    const root = b.root
    const initial = applyClosedTermIntro(b.build(), root, p('\\x. x'))
    const boundary = `${root}_intro`
    const node = `${root}_intro`
    const side = mkDiagramWithBoundary(initial, [boundary])
    const session = startSession(side, side, { theorems: new Map(), relations: new Map() })
    const action: ProofAction = {
      label: 'replace the boundary identity',
      steps: [
        { rule: 'erasure', sel: { region: root, regions: [], nodes: [node], wires: [boundary] } },
        { rule: 'closedTermIntro', region: root, term: p('\\x. x') },
      ],
      placements: [],
    }

    const finalOnly = applyAction(initial, action, session.ctx)
    expect(finalOnly.wires[boundary]).toBeDefined()
    expect(() => applyForwardAction(session, action))
      .toThrowError(new RegExp(`forward step 0 gives boundary wire '${boundary}' no semantic image`))
    expect(session.forward.actions).toHaveLength(0)
  })

  it('undo pops exactly one step and restores the prior diagram', () => {
    const theory = buildFregeTheory()
    const ctx = verifyTheory(theory)
    const { lhs, rhs } = goalPair()
    const s0 = startSession(lhs, rhs, ctx)
    const s1 = applyForward(s0, {
      rule: 'doubleCutIntro',
      sel: mkSelection(currentSide(s0, 'forward'), { region: currentSide(s0, 'forward').root, regions: [], nodes: [], wires: [] }),
    })
    const s2 = undoForward(s1)
    expect(s2.forward.actions).toHaveLength(1)
    expect(timelineActiveActions(s2.forward)).toHaveLength(0)
    expect(currentSide(s2, 'forward')).toBe(currentSide(s0, 'forward'))
    expect(() => undoForward(s2)).toThrowError(/nothing to undo/)
  })

  it('cites bundled theorems as single steps', async () => {
    const { ctx } = await bootFixture()
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, YF)
    const wo = h.wire(h.root, [{ node: n, port: { kind: 'output' } }])
    const wf = h.wire(h.root, [{ node: n, port: { kind: 'freeVar', name: 'f' } }])
    const start = mkDiagramWithBoundary(h.build(), [wo, wf])
    const target = start // rhs irrelevant for this check
    let s = startSession(start, target, ctx)
    s = applyForward(s, {
      rule: 'theorem', name: 'fixedPoint', direction: 'forward',
      at: { sel: mkSelection(currentSide(s, 'forward'), { region: currentSide(s, 'forward').root, regions: [], nodes: [n], wires: [] }), args: [wo, wf] },
    })
    expect(Object.values(currentSide(s, 'forward').nodes).some((nd) => nd.kind === 'term' && termEq(nd.term, FYF))).toBe(true)
  })
})

describe('backward mode', () => {
  it('un-wraps a double cut backward, recording the forward intro step', () => {
    const theory = buildFregeTheory()
    const ctx = verifyTheory(theory)
    const { lhs, rhs } = goalPair()
    let s = startSession(lhs, rhs, ctx)
    // the goal has the node + an empty double cut: backward double-cut ELIM
    // is the inverse of forward INTRO... no: backward we REMOVE structure the
    // forward direction would ADD. Removing the goal's double cut backward
    // records the forward doubleCutIntro that re-creates it.
    const outer = Object.entries(currentSide(s, 'backward').regions).find(
      ([, r]) => r.kind === 'cut' && r.parent === currentSide(s, 'backward').root,
    )![0]
    s = applyBackward(s, { rule: 'doubleCutElim', region: outer })
    expect(timelineActiveActions(s.backward)).toHaveLength(1)
    expect(timelineActiveActions(s.backward)[0]!.steps[0]!.rule).toBe('doubleCutElim')
    expect(Object.keys(currentSide(s, 'backward').regions)).toHaveLength(1)
    // and now the two sides meet: lhs ≅ unwrapped rhs
    expect(meet(s)).toBe(true)
    const thm = assembleTheorem(s, 'toy2')
    expect(thm.actions).toHaveLength(0)
    expect(thm.backActions).toHaveLength(1)
  })

  it('backward undo restores the prior goal diagram', () => {
    const theory = buildFregeTheory()
    const ctx = verifyTheory(theory)
    const { lhs, rhs } = goalPair()
    let s = startSession(lhs, rhs, ctx)
    const outer = Object.entries(currentSide(s, 'backward').regions).find(
      ([, r]) => r.kind === 'cut' && r.parent === currentSide(s, 'backward').root,
    )![0]
    const before = currentSide(s, 'backward')
    s = applyBackward(s, { rule: 'doubleCutElim', region: outer })
    s = undoBackward(s)
    expect(currentSide(s, 'backward')).toBe(before)
    expect(s.backward.actions).toHaveLength(1)
    expect(timelineActiveActions(s.backward)).toHaveLength(0)
  })
})

describe('multi-step backward composition', () => {
  it('two backward actions assemble into a checkable theorem', () => {
    const theory = buildFregeTheory()
    const ctx = verifyTheory(theory)
    // lhs: bare node; rhs: the node wrapped in TWO nested double cuts
    const l = new DiagramBuilder()
    l.termNode(l.root, p('\\x. x'))
    const lhs = mkDiagramWithBoundary(l.build(), [])
    const r = new DiagramBuilder()
    const m = r.termNode(r.root, p('\\x. x'))
    const o1 = r.cut(r.root)
    const i1 = r.cut(o1)
    const o2 = r.cut(i1)
    r.cut(o2)
    void m
    const rhs = mkDiagramWithBoundary(r.build(), [])
    let s = startSession(lhs, rhs, ctx)
    // unwrap the INNER pair first, then the outer pair
    s = applyBackward(s, { rule: 'doubleCutElim', region: o2 })
    s = applyBackward(s, { rule: 'doubleCutElim', region: o1 })
    expect(timelineActiveActions(s.backward)).toHaveLength(2)
    expect(meet(s)).toBe(true)
    const thm = assembleTheorem(s, 'doubleWrap')
    expect(thm.actions).toHaveLength(0)
    expect(thm.backActions).toHaveLength(2)
    expect(() => checkTheorem(thm, ctx)).not.toThrow()
  })

  it('assembleTheorem refuses when the sides have not met', () => {
    const theory = buildFregeTheory()
    const ctx = verifyTheory(theory)
    const l = new DiagramBuilder()
    l.termNode(l.root, p('\\x. x'))
    const lhs = mkDiagramWithBoundary(l.build(), [])
    const r = new DiagramBuilder()
    r.termNode(r.root, p('\\x. \\y. x'))
    const rhs = mkDiagramWithBoundary(r.build(), [])
    const s = startSession(lhs, rhs, ctx)
    expect(() => assembleTheorem(s, 'nope')).toThrowError(/have not met/)
  })
})

describe('backward undo restores the composed tail', () => {
  it('undo then a DIFFERENT redo keeps the tail consistent', () => {
    const theory = buildFregeTheory()
    const ctx = verifyTheory(theory)
    const l = new DiagramBuilder()
    l.termNode(l.root, p('\\x. x'))
    const lhs = mkDiagramWithBoundary(l.build(), [])
    const r = new DiagramBuilder()
    const m = r.termNode(r.root, p('\\x. x'))
    const o1 = r.cut(r.root)
    const i1 = r.cut(o1)
    const o2 = r.cut(i1)
    r.cut(o2)
    void m
    const rhs = mkDiagramWithBoundary(r.build(), [])
    let s = startSession(lhs, rhs, ctx)
    s = applyBackward(s, { rule: 'doubleCutElim', region: o2 })
    s = applyBackward(s, { rule: 'doubleCutElim', region: o1 })
    s = undoBackward(s)
    expect(s.backward.actions).toHaveLength(2)
    expect(timelineActiveActions(s.backward)).toHaveLength(1)
    // redo: the remaining pair is o1's (the inner one was restored by undo? no —
    // undo restored the state AFTER unwrapping o2 only, so o1's pair remains)
    s = applyBackward(s, { rule: 'doubleCutElim', region: o1 })
    expect(meet(s)).toBe(true)
    const thm = assembleTheorem(s, 'redo')
    expect(() => checkTheorem(thm, ctx)).not.toThrow()
  })
})

describe('backward spawning, un-conversion, un-citation', () => {
  it('atomic spawning adds open content backward and records the same shared rule', () => {
    const ctx = verifyTheory(buildFregeTheory())
    // goal: a single node; backward: the proof "had" an extra node erased
    const l = new DiagramBuilder()
    const l0 = l.termNode(l.root, p('\\x. x'))
    l.wire(l.root, [{ node: l0, port: { kind: 'output' } }])
    const both = new DiagramBuilder()
    const b0 = both.termNode(both.root, p('\\x. x'))
    both.wire(both.root, [{ node: b0, port: { kind: 'output' } }])
    const bx = both.termNode(both.root, p('x'))
    both.wire(both.root, [{ node: bx, port: { kind: 'output' } }])
    both.wire(both.root, [{ node: bx, port: { kind: 'freeVar', name: 'x' } }])
    const lhs = mkDiagramWithBoundary(both.build(), [])
    const rhs = mkDiagramWithBoundary(l.build(), [])
    let s = startSession(lhs, rhs, ctx)
    s = applyBackward(s, {
      rule: 'openTermSpawn',
      region: currentSide(s, 'backward').root,
      term: p('x'),
    })
    expect(timelineActiveActions(s.backward)[0]!.steps[0]!.rule).toBe('openTermSpawn')
    expect(meet(s)).toBe(true)
    const thm = assembleTheorem(s, 'unErased')
    expect(() => checkTheorem(thm, ctx)).not.toThrow()
  })

  it('un-conversion rewrites a node term backward with a swapped certificate', () => {
    const ctx = verifyTheory(buildFregeTheory())
    const l = new DiagramBuilder()
    l.termNode(l.root, p('(\\a. a) y'))
    const lhs = mkDiagramWithBoundary(l.build(), [])
    const r = new DiagramBuilder()
    const m = r.termNode(r.root, p('y'))
    const rhs = mkDiagramWithBoundary(r.build(), [])
    let s = startSession(lhs, rhs, ctx)
    // the goal node's source free 'y' is canonical s0; the backward target
    // must be spelled in the node's CURRENT port names
    const conv = applyConversion(currentSide(s, 'backward'), m, p('(\\a. a) s0'), 32)
    s = applyBackward(s, { rule: 'conversion', node: m, term: p('(\\a. a) s0'), certificate: conv.certificate, attachments: {} })
    expect(timelineActiveActions(s.backward)[0]!.steps[0]!.rule).toBe('conversion')
    expect(meet(s)).toBe(true)
    const thm = assembleTheorem(s, 'unConverted')
    expect(() => checkTheorem(thm, ctx)).not.toThrow()
  })

  it('un-citation replaces a theorem rhs-occurrence by its lhs in the goal', async () => {
    const { ctx } = await bootFixture()
    // lhs: a `Y f` node. rhs (goal): fixedPoint's conclusion (an `f (Y f)` node)
    // — built by citing forward once, then used as the goal of a FRESH session
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, YF)
    const wo = h.wire(h.root, [{ node: n, port: { kind: 'output' } }])
    const wf = h.wire(h.root, [{ node: n, port: { kind: 'freeVar', name: 'f' } }])
    const lhs = mkDiagramWithBoundary(h.build(), [wo, wf])
    let warm = startSession(lhs, lhs, ctx)
    warm = applyForward(warm, {
      rule: 'theorem', name: 'fixedPoint', direction: 'forward',
      at: { sel: mkSelection(currentSide(warm, 'forward'), { region: currentSide(warm, 'forward').root, regions: [], nodes: [n], wires: [] }), args: [wo, wf] },
    })
    const rhs = mkDiagramWithBoundary(currentSide(warm, 'forward'), [wo, wf])
    let s = startSession(lhs, rhs, ctx)
    // pick the rhs occurrence in the GOAL: the f (Y f) node on the boundary lines
    const g = currentSide(s, 'backward')
    const two = Object.entries(g.nodes).find(([, nd]) => nd.kind === 'term' && termEq(nd.term, FYF))![0]
    s = applyBackward(s, {
      rule: 'theorem',
      name: 'fixedPoint',
      direction: 'reverse',
      at: {
        sel: { region: g.root, regions: [], nodes: [two], wires: [] },
        args: [wo, wf],
      },
    })
    expect(timelineActiveActions(s.backward)[0]!.steps[0]!.rule).toBe('theorem')
    expect(meet(s)).toBe(true)
    const thm = assembleTheorem(s, 'unCited')
    expect(() => checkTheorem(thm, ctx)).not.toThrow()
  })
})

describe('unCite refusals', () => {
  it('refuses unCite at a negative region', async () => {
    const { ctx } = await bootFixture()
    // goal: a TWO node wrapped in a cut (negative region is the cut interior)
    const h = new DiagramBuilder()
    const nz = h.termNode(h.root, TWOc)
    const wz = h.wire(h.root, [{ node: nz, port: { kind: 'output' } }])
    const lhs = mkDiagramWithBoundary(h.build(), [wz])
    const r = new DiagramBuilder()
    const nz2 = r.termNode(r.root, TWOc)
    const wz2 = r.wire(r.root, [{ node: nz2, port: { kind: 'output' } }])
    const cut = r.cut(r.root)
    const rhs = mkDiagramWithBoundary(r.build(), [wz2])
    const s = startSession(lhs, rhs, ctx)
    const g = currentSide(s, 'backward')
    const cutId = Object.entries(g.regions).find(([, reg]) => reg.kind === 'cut' && reg.parent === g.root)![0]
    void wz2; void cut
    expect(() =>
      applyBackward(s, {
        rule: 'theorem',
        name: 'onePlusOne',
        direction: 'reverse',
        at: {
          sel: { region: cutId, regions: [], nodes: [], wires: [] },
          args: [],
        },
      })
    ).toThrowError(/positive region/)
  })

  it('refuses unCite when the selection is not an rhs occurrence', async () => {
    const { ctx } = await bootFixture()
    // goal: a ZERO node; selection is the node itself — not onePlusOne's rhs (TWO)
    const h = new DiagramBuilder()
    const nz = h.termNode(h.root, ZEROc)
    const wz = h.wire(h.root, [{ node: nz, port: { kind: 'output' } }])
    const lhsD = h.build()
    const lhs = mkDiagramWithBoundary(lhsD, [wz])
    const s = startSession(lhs, lhs, ctx)
    const g = currentSide(s, 'backward')
    expect(() =>
      applyBackward(s, {
        rule: 'theorem',
        name: 'onePlusOne',
        direction: 'reverse',
        at: {
          sel: { region: g.root, regions: [], nodes: [nz], wires: [wz] },
          args: [],
        },
      })
    ).toThrowError(/not an occurrence/)
  })
})

describe('sideBoundary — prove-mode sides render their statement boundary', () => {
  it('forward reads the lhs boundary, backward reads the rhs boundary', () => {
    const theory = buildFregeTheory()
    const ctx = verifyTheory(theory)
    const plusComm = theory.theorems.find((t) => t.name === 'plusComm')!
    const s = startSession(plusComm.lhs, plusComm.rhs, ctx)
    expect(sideBoundary(s, 'forward')).toBe(s.lhs.boundary)
    expect(sideBoundary(s, 'backward')).toBe(s.rhs.boundary)
  })

})

describe('backward proving takes the full vocabulary (shared implementation, flipped gates)', () => {
  const ctx = () => verifyTheory(buildFregeTheory())

  it('erasure applies in NEGATIVE regions backward and declares green', () => {
    // goal: T at root + cut containing M; lhs: T + empty cut
    const r = new DiagramBuilder()
    const t = r.termNode(r.root, p('\\x. x'))
    r.wire(r.root, [{ node: t, port: { kind: 'output' } }])
    const cut = r.cut(r.root)
    const m = r.termNode(cut, p('\\y. y'))
    const wm = r.wire(cut, [{ node: m, port: { kind: 'output' } }])
    const rhs = mkDiagramWithBoundary(r.build(), [])
    const l = new DiagramBuilder()
    const t2 = l.termNode(l.root, p('\\x. x'))
    l.wire(l.root, [{ node: t2, port: { kind: 'output' } }])
    l.cut(l.root)
    const lhs = mkDiagramWithBoundary(l.build(), [])
    let s = startSession(lhs, rhs, ctx())
    s = applyBackward(s, { rule: 'erasure', sel: { region: cut, regions: [], nodes: [m], wires: [wm] } })
    expect(timelineActiveActions(s.backward)[0]!.steps[0]!.rule).toBe('erasure')
    expect(meet(s)).toBe(true)
    const thm = assembleTheorem(s, 'backwardErased')
    expect(() => checkTheorem(thm, ctx())).not.toThrow()
  })

  it('refuses backward erasure in a POSITIVE region (the flipped gate)', () => {
    const r = new DiagramBuilder()
    const t = r.termNode(r.root, p('\\x. x'))
    const wt = r.wire(r.root, [{ node: t, port: { kind: 'output' } }])
    const rhs = mkDiagramWithBoundary(r.build(), [])
    const s = startSession(rhs, rhs, ctx())
    expect(() =>
      applyBackward(s, { rule: 'erasure', sel: { region: currentSide(s, 'backward').root, regions: [], nodes: [t], wires: [wt] } }),
    ).toThrowError(/backward erasure requires a negative region/)
  })

  it('backward iteration records deiteration and declares green', () => {
    // goal: A at root + empty cut; lhs: A + cut containing the copy
    const r = new DiagramBuilder()
    const a = r.termNode(r.root, p('\\x. x'))
    const wa = r.wire(r.root, [{ node: a, port: { kind: 'output' } }])
    const cut = r.cut(r.root)
    const rhs = mkDiagramWithBoundary(r.build(), [])
    const l = new DiagramBuilder()
    const a2 = l.termNode(l.root, p('\\x. x'))
    l.wire(l.root, [{ node: a2, port: { kind: 'output' } }])
    const lcut = l.cut(l.root)
    const a3 = l.termNode(lcut, p('\\x. x'))
    l.wire(lcut, [{ node: a3, port: { kind: 'output' } }])
    const lhs = mkDiagramWithBoundary(l.build(), [])
    let s = startSession(lhs, rhs, ctx())
    s = applyBackward(s, { rule: 'iteration', sel: { region: currentSide(s, 'backward').root, regions: [], nodes: [a], wires: [wa] }, target: cut })
    expect(timelineActiveActions(s.backward)[0]!.steps[0]!.rule).toBe('iteration')
    expect(meet(s)).toBe(true)
    const thm = assembleTheorem(s, 'backwardIterated')
    expect(() => checkTheorem(thm, ctx())).not.toThrow()
  })

  it('backward deiteration finds the surviving justifier and records iteration', () => {
    // goal: A at root + cut containing exact copy; lhs: A + empty cut
    const r = new DiagramBuilder()
    const a = r.termNode(r.root, p('\\x. x'))
    r.wire(r.root, [{ node: a, port: { kind: 'output' } }])
    const cut = r.cut(r.root)
    const c = r.termNode(cut, p('\\x. x'))
    const wc = r.wire(cut, [{ node: c, port: { kind: 'output' } }])
    const rhs = mkDiagramWithBoundary(r.build(), [])
    const l = new DiagramBuilder()
    const a2 = l.termNode(l.root, p('\\x. x'))
    l.wire(l.root, [{ node: a2, port: { kind: 'output' } }])
    l.cut(l.root)
    const lhs = mkDiagramWithBoundary(l.build(), [])
    let s = startSession(lhs, rhs, ctx())
    const deSel = { region: cut, regions: [], nodes: [c], wires: [wc] }
    s = applyBackward(s, certifiedDeiterationStep(currentSide(s, 'backward'), deSel, 64))
    expect(timelineActiveActions(s.backward)[0]!.steps[0]!.rule).toBe('deiteration')
    expect(meet(s)).toBe(true)
    const thm = assembleTheorem(s, 'backwardDeiterated')
    expect(() => checkTheorem(thm, ctx())).not.toThrow()
  })

  it('backward doubleCutIntro records the elimination', () => {
    const r = new DiagramBuilder()
    const a = r.termNode(r.root, p('\\x. x'))
    const wa = r.wire(r.root, [{ node: a, port: { kind: 'output' } }])
    const rhs = mkDiagramWithBoundary(r.build(), [])
    const l = new DiagramBuilder()
    const c1 = l.cut(l.root)
    const c2 = l.cut(c1)
    const a2 = l.termNode(c2, p('\\x. x'))
    // the intro keeps the selected wire at its OLD scope (the ∃ passes
    // through the annulus), so the lhs scopes it at the root
    l.wire(l.root, [{ node: a2, port: { kind: 'output' } }])
    const lhs = mkDiagramWithBoundary(l.build(), [])
    let s = startSession(lhs, rhs, ctx())
    s = applyBackward(s, { rule: 'doubleCutIntro', sel: { region: currentSide(s, 'backward').root, regions: [], nodes: [a], wires: [wa] } })
    expect(timelineActiveActions(s.backward)[0]!.steps[0]!.rule).toBe('doubleCutIntro')
    expect(meet(s)).toBe(true)
    const thm = assembleTheorem(s, 'backwardWrapped')
    expect(() => checkTheorem(thm, ctx())).not.toThrow()
  })

  it('every rule runs backward — only polarity gates flip (wireSever needs NEGATIVE scope backward)', () => {
    const r = new DiagramBuilder()
    const a = r.termNode(r.root, p('x y'))
    const wa = r.wire(r.root, [
      { node: a, port: { kind: 'freeVar', name: 'x' } },
      { node: a, port: { kind: 'freeVar', name: 'y' } },
    ])
    r.wire(r.root, [{ node: a, port: { kind: 'output' } }])
    const rhs = mkDiagramWithBoundary(r.build(), [])
    const s = startSession(rhs, rhs, ctx())
    expect(() =>
      applyBackward(s, { rule: 'wireSever', wire: wa, keep: [{ node: a, port: { kind: 'freeVar', name: 's0' } }] }),
    ).toThrowError(/backward severing a wire requires a negative scope/)
  })
})

describe('backward erasure of externally-bound atoms (binder stubs)', () => {
  it('backward erasure rebinds the atom to its bubble (user bug: iterate a bound predicate, delete it)', () => {
    const c = verifyTheory(buildFregeTheory())
    // goal: cut > bubble(1) > two bound atoms sharing a line
    const r = new DiagramBuilder()
    const cut = r.cut(r.root)
    const bub = r.bubble(cut, 1)
    const a1 = r.atom(bub, bub)
    const a2 = r.atom(bub, bub)
    const w = r.wire(bub, [
      { node: a1, port: { kind: 'arg', index: 0 } },
      { node: a2, port: { kind: 'arg', index: 0 } },
    ])
    const rhs = mkDiagramWithBoundary(r.build(), [])
    // lhs: the same shape with a2 gone (the wire keeps a1)
    const l = new DiagramBuilder()
    const lcut = l.cut(l.root)
    const lbub = l.bubble(lcut, 1)
    const b1 = l.atom(lbub, lbub)
    l.wire(lbub, [{ node: b1, port: { kind: 'arg', index: 0 } }])
    const lhs = mkDiagramWithBoundary(l.build(), [])
    let s = startSession(lhs, rhs, c)
    void w
    // the bubble sits inside a cut: NEGATIVE — backward erasure's gate
    s = applyBackward(s, { rule: 'erasure', sel: { region: bub, regions: [], nodes: [a2], wires: [] } })
    expect(timelineActiveActions(s.backward)[0]!.steps[0]!.rule).toBe('erasure')
    expect(meet(s)).toBe(true)
    const thm = assembleTheorem(s, 'boundAtomErased')
    expect(() => checkTheorem(thm, c)).not.toThrow()
  })
})

describe('dual-replay redesign: record actions, verify from both ends', () => {
  it("the user's scenario: backward-deiterate a bound predicate copy in a POSITIVE sheet", () => {
    const c = verifyTheory(buildFregeTheory())
    // goal (positive sheet): bubble with TWO bound atoms on one line — as
    // after iterating a bound predicate into its own scope
    const r = new DiagramBuilder()
    const bub = r.bubble(r.root, 1)
    const a1 = r.atom(bub, bub)
    const a2 = r.atom(bub, bub)
    const w = r.wire(bub, [
      { node: a1, port: { kind: 'arg', index: 0 } },
      { node: a2, port: { kind: 'arg', index: 0 } },
    ])
    const rhs = mkDiagramWithBoundary(r.build(), [])
    const l = new DiagramBuilder()
    const lbub = l.bubble(l.root, 1)
    const b1 = l.atom(lbub, lbub)
    l.wire(lbub, [{ node: b1, port: { kind: 'arg', index: 0 } }])
    const lhs = mkDiagramWithBoundary(l.build(), [])
    let s = startSession(lhs, rhs, c)
    void w
    // erase is gated out (positive+backward needs negative) — deletion here IS
    // deiteration, justified by the surviving copy at the same scope
    const deSel = { region: bub, regions: [], nodes: [a2], wires: [] }
    s = applyBackward(s, certifiedDeiterationStep(currentSide(s, 'backward'), deSel, 64))
    expect(timelineActiveActions(s.backward)[0]!.steps[0]!.rule).toBe('deiteration')
    expect(meet(s)).toBe(true)
    const thm = assembleTheorem(s, 'boundCopyDeiterated')
    expect(() => checkTheorem(thm, c)).not.toThrow()
  })

  it('tampered backActions cannot certify: the dual replay is the authority', () => {
    const c = verifyTheory(buildFregeTheory())
    const r = new DiagramBuilder()
    const t = r.termNode(r.root, p('\\x. x'))
    r.wire(r.root, [{ node: t, port: { kind: 'output' } }])
    const cut = r.cut(r.root)
    const m = r.termNode(cut, p('\\y. y'))
    const wm = r.wire(cut, [{ node: m, port: { kind: 'output' } }])
    const rhs = mkDiagramWithBoundary(r.build(), [])
    const l = new DiagramBuilder()
    const t2 = l.termNode(l.root, p('\\x. x'))
    l.wire(l.root, [{ node: t2, port: { kind: 'output' } }])
    l.cut(l.root)
    const lhs = mkDiagramWithBoundary(l.build(), [])
    let s = startSession(lhs, rhs, c)
    s = applyBackward(s, { rule: 'erasure', sel: { region: cut, regions: [], nodes: [m], wires: [wm] } })
    const thm = assembleTheorem(s, 'honest')
    expect(() => checkTheorem(thm, c)).not.toThrow()
    // drop the backward step: the halves no longer meet
    const forged = { ...thm, backActions: [] }
    expect(() => checkTheorem(forged, c)).toThrowError(/do not meet|does not arrive/)
    // flip the gate: an erasure claimed at a POSITIVE region cannot replay backward
    const forged2 = { ...thm, backActions: [gesture({ rule: 'erasure', sel: { region: rhs.diagram.root, regions: [], nodes: [t], wires: [] } })] }
    expect(() => checkTheorem(forged2, c)).toThrowError(/backward erasure requires a negative region/)
  })
})
