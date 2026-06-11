import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { buildFregeTheory } from '../../src/theories/frege'
import { verifyTheory } from '../../src/kernel/proof/store'
import { startSession, applyForward, applyBackward, undoForward, undoBackward, meet, assembleTheorem } from '../../src/app/session'
import { checkTheorem } from '../../src/kernel/proof/theorem'

const consts = new Set(['ZERO', 'SUCC', 'PLUS', 'ONE', 'TWO'])
const p = (s: string) => parseTerm(s, consts)

function goalPair() {
  // goal: o = PLUS ONE ONE node ⟹ same node double-cut-wrapped (a toy goal)
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
    expect(s0.forward.steps).toHaveLength(0)
    const s1 = applyForward(s0, {
      rule: 'doubleCutIntro',
      sel: mkSelection(s0.forward.current, { region: s0.forward.current.root, regions: [], nodes: [], wires: [] }),
    })
    expect(s1.forward.steps).toHaveLength(1)
    expect(Object.keys(s1.forward.current.regions).length).toBe(3)
  })

  it('meets when forward reaches the rhs and assembles a checkable theorem', () => {
    const theory = buildFregeTheory()
    const ctx = verifyTheory(theory)
    const { lhs, rhs } = goalPair()
    let s = startSession(lhs, rhs, ctx)
    expect(meet(s)).toBe(false)
    s = applyForward(s, {
      rule: 'doubleCutIntro',
      sel: mkSelection(s.forward.current, { region: s.forward.current.root, regions: [], nodes: [], wires: [] }),
    })
    expect(meet(s)).toBe(true)
    const thm = assembleTheorem(s, 'toy')
    expect(thm.steps.length).toBeGreaterThan(0)
    expect(thm.name).toBe('toy')
  })

  it('forward refusals surface the kernel message and leave the session unchanged', () => {
    const theory = buildFregeTheory()
    const ctx = verifyTheory(theory)
    const { lhs, rhs, n } = goalPair()
    const s0 = startSession(lhs, rhs, ctx)
    expect(() => applyForward(s0, {
      rule: 'insertion',
      region: s0.forward.current.root,
      pattern: lhs, attachments: [], binders: {},
    })).toThrowError(/insertion requires a negative region/)
    expect(s0.forward.steps).toHaveLength(0)
    void n
  })

  it('undo pops exactly one step and restores the prior diagram', () => {
    const theory = buildFregeTheory()
    const ctx = verifyTheory(theory)
    const { lhs, rhs } = goalPair()
    const s0 = startSession(lhs, rhs, ctx)
    const s1 = applyForward(s0, {
      rule: 'doubleCutIntro',
      sel: mkSelection(s0.forward.current, { region: s0.forward.current.root, regions: [], nodes: [], wires: [] }),
    })
    const s2 = undoForward(s1)
    expect(s2.forward.steps).toHaveLength(0)
    expect(s2.forward.current).toBe(s0.forward.current)
    expect(() => undoForward(s2)).toThrowError(/nothing to undo/)
  })

  it('cites bundled theorems as single steps', () => {
    const theory = buildFregeTheory()
    const ctx = verifyTheory(theory)
    const h = new DiagramBuilder()
    const nz = h.termNode(h.root, p('ZERO'))
    const wz = h.wire(h.root, [{ node: nz, port: { kind: 'output' } }])
    const start = mkDiagramWithBoundary(h.build(), [wz])
    const target = start // rhs irrelevant for this check
    let s = startSession(start, target, ctx)
    s = applyForward(s, {
      rule: 'theorem', name: 'zeroIsNat', direction: 'forward',
      at: { sel: mkSelection(s.forward.current, { region: s.forward.current.root, regions: [], nodes: [nz], wires: [] }), args: [wz] },
    })
    expect(Object.values(s.forward.current.regions).some((r) => r.kind === 'bubble')).toBe(true)
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
    const outer = Object.entries(s.backward.current.regions).find(
      ([, r]) => r.kind === 'cut' && r.parent === s.backward.current.root,
    )![0]
    s = applyBackward(s, { kind: 'unDoubleCut', outer })
    expect(s.backward.steps).toHaveLength(1)
    expect(s.backward.steps[0]!.rule).toBe('doubleCutIntro')
    expect(Object.keys(s.backward.current.regions)).toHaveLength(1)
    // and now the two sides meet: lhs ≅ unwrapped rhs
    expect(meet(s)).toBe(true)
    const thm = assembleTheorem(s, 'toy2')
    expect(thm.steps).toHaveLength(1)
  })

  it('backward undo restores the prior goal diagram', () => {
    const theory = buildFregeTheory()
    const ctx = verifyTheory(theory)
    const { lhs, rhs } = goalPair()
    let s = startSession(lhs, rhs, ctx)
    const outer = Object.entries(s.backward.current.regions).find(
      ([, r]) => r.kind === 'cut' && r.parent === s.backward.current.root,
    )![0]
    const before = s.backward.current
    s = applyBackward(s, { kind: 'unDoubleCut', outer })
    s = undoBackward(s)
    expect(s.backward.current).toBe(before)
    expect(s.backward.steps).toHaveLength(0)
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
    s = applyBackward(s, { kind: 'unDoubleCut', outer: o2 })
    s = applyBackward(s, { kind: 'unDoubleCut', outer: o1 })
    expect(s.backward.steps).toHaveLength(2)
    expect(meet(s)).toBe(true)
    const thm = assembleTheorem(s, 'doubleWrap')
    expect(thm.steps).toHaveLength(2)
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
