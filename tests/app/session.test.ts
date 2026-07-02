import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { buildFregeTheory } from '../../src/theories/frege'
import { verifyTheory } from '../../src/kernel/proof/store'
import { termEq } from '../../src/kernel/term/term'
import { bootFixture } from './boot-fixture'
import { startSession, applyForward, applyBackward, undoForward, undoBackward, meet, assembleTheorem, sideBoundary } from '../../src/app/session'
import { checkTheorem } from '../../src/kernel/proof/theorem'
import { mkEngine, settle, paint, LIGHT } from '../../src/view/index'

const p = (s: string) => parseTerm(s, new Set<string>())
// pure Church fixtures for the onePlusOne demo (no term constants)
const POO = p('(\\m. \\n. \\f. \\x. m f (n f x)) (\\f. \\x. f x) (\\f. \\x. f x)')
const TWOc = p('\\f. \\x. f (f x)')
const ZEROc = p('\\f. \\x. x')

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

  it('cites bundled theorems as single steps', async () => {
    const { ctx } = await bootFixture()
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, POO)
    const wo = h.wire(h.root, [{ node: n, port: { kind: 'output' } }])
    const start = mkDiagramWithBoundary(h.build(), [wo])
    const target = start // rhs irrelevant for this check
    let s = startSession(start, target, ctx)
    s = applyForward(s, {
      rule: 'theorem', name: 'onePlusOne', direction: 'forward',
      at: { sel: mkSelection(s.forward.current, { region: s.forward.current.root, regions: [], nodes: [n], wires: [] }), args: [wo] },
    })
    expect(Object.values(s.forward.current.nodes).some((nd) => nd.kind === 'term' && termEq(nd.term, TWOc))).toBe(true)
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
    s = applyBackward(s, { kind: 'unDoubleCut', outer: o2 })
    s = applyBackward(s, { kind: 'unDoubleCut', outer: o1 })
    s = undoBackward(s)
    expect(s.backward.composedTail).toHaveLength(1)
    // redo: the remaining pair is o1's (the inner one was restored by undo? no —
    // undo restored the state AFTER unwrapping o2 only, so o1's pair remains)
    s = applyBackward(s, { kind: 'unDoubleCut', outer: o1 })
    expect(meet(s)).toBe(true)
    const thm = assembleTheorem(s, 'redo')
    expect(() => checkTheorem(thm, ctx)).not.toThrow()
  })
})

describe('backward un-erase, un-conversion, un-citation', () => {
  it('un-erase adds content backward and records the forward erasure', () => {
    const ctx = verifyTheory(buildFregeTheory())
    // goal: a single node; backward: the proof "had" an extra node erased
    const l = new DiagramBuilder()
    l.termNode(l.root, p('\\x. x'))
    const both = new DiagramBuilder()
    both.termNode(both.root, p('\\x. x'))
    both.termNode(both.root, p('\\x. \\y. x'))
    const lhs = mkDiagramWithBoundary(both.build(), [])
    const rhs = mkDiagramWithBoundary(l.build(), [])
    let s = startSession(lhs, rhs, ctx)
    const pat = new DiagramBuilder()
    pat.termNode(pat.root, p('\\x. \\y. x'))
    s = applyBackward(s, {
      kind: 'unErase',
      region: s.backward.current.root,
      pattern: mkDiagramWithBoundary(pat.build(), []),
      attachments: [],
    })
    expect(s.backward.steps[0]!.rule).toBe('erasure')
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
    s = applyBackward(s, { kind: 'unConvert', node: m, term: p('(\\a. a) s0'), fuel: 32 })
    expect(s.backward.steps[0]!.rule).toBe('conversion')
    expect(meet(s)).toBe(true)
    const thm = assembleTheorem(s, 'unConverted')
    expect(() => checkTheorem(thm, ctx)).not.toThrow()
  })

  it('un-citation replaces a theorem rhs-occurrence by its lhs in the goal', async () => {
    const { ctx } = await bootFixture()
    // lhs: a PLUS ONE ONE node. rhs (goal): onePlusOne's conclusion (a TWO node) —
    // built by citing forward once, then used as the goal of a FRESH session
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, POO)
    const wo = h.wire(h.root, [{ node: n, port: { kind: 'output' } }])
    const lhs = mkDiagramWithBoundary(h.build(), [wo])
    let warm = startSession(lhs, lhs, ctx)
    warm = applyForward(warm, {
      rule: 'theorem', name: 'onePlusOne', direction: 'forward',
      at: { sel: mkSelection(warm.forward.current, { region: warm.forward.current.root, regions: [], nodes: [n], wires: [] }), args: [wo] },
    })
    const rhs = mkDiagramWithBoundary(warm.forward.current, [wo])
    let s = startSession(lhs, rhs, ctx)
    // pick the rhs occurrence in the GOAL: the TWO node on the boundary line
    const g = s.backward.current
    const two = Object.entries(g.nodes).find(([, nd]) => nd.kind === 'term' && termEq(nd.term, TWOc))![0]
    s = applyBackward(s, {
      kind: 'unCite',
      name: 'onePlusOne',
      at: {
        sel: { region: g.root, regions: [], nodes: [two], wires: [] },
        args: [wo],
      },
    })
    expect(s.backward.steps[0]!.rule).toBe('theorem')
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
    const g = s.backward.current
    const cutId = Object.entries(g.regions).find(([, reg]) => reg.kind === 'cut' && reg.parent === g.root)![0]
    void wz2; void cut
    expect(() =>
      applyBackward(s, {
        kind: 'unCite',
        name: 'onePlusOne',
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
    const g = s.backward.current
    expect(() =>
      applyBackward(s, {
        kind: 'unCite',
        name: 'onePlusOne',
        at: {
          sel: { region: g.root, regions: [], nodes: [nz], wires: [] },
          args: [wz],
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

  it('an engine built for a side renders exactly one frame exit per boundary wire', () => {
    const theory = buildFregeTheory()
    const ctx = verifyTheory(theory)
    const plusComm = theory.theorems.find((t) => t.name === 'plusComm')!
    const s = startSession(plusComm.lhs, plusComm.rhs, ctx)
    const boundary = sideBoundary(s, 'backward')
    expect(boundary.length).toBeGreaterThan(0)
    const e = mkEngine(s.backward.current, boundary)
    settle(e, 1200)
    expect(paint(e, LIGHT).filter((sh) => sh.kind === 'exit')).toHaveLength(boundary.length)
  })
})
