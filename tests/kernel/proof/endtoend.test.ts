import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { diagramFingerprint } from '../../../src/kernel/diagram/canonical/fingerprint'
import {
  replayProof, composeProofs, checkTheorem, verifyTheory, loadTheory, theoryToJson,
} from '../../../src/kernel/proof/index'
import type { ProofStep, Theorem, Theory } from '../../../src/kernel/proof/index'

const p = (s: string) => parseTerm(s)

describe('end to end: a sentence theorem built bidirectionally', () => {
  it('blank ⟹ ¬¬(empty cut pair) via forward and backward halves meeting in the middle', () => {
    // statement: from the empty sheet, derive a bare double cut.
    const blank = new DiagramBuilder().build()
    const goalBuilder = new DiagramBuilder()
    const outer = goalBuilder.cut(goalBuilder.root)
    goalBuilder.cut(outer)
    const goal = goalBuilder.build()

    // forward half: nothing (stay at blank). backward half, recorded against
    // an INDEPENDENTLY built blank (different from the forward side's blank
    // only in construction history — ids are deterministic, so exercise the
    // composition machinery anyway):
    const backwardStart = new DiagramBuilder().build()
    const tail: ProofStep[] = [{
      rule: 'doubleCutIntro',
      sel: mkSelection(backwardStart, { region: backwardStart.root, regions: [], nodes: [], wires: [] }),
    }]
    const composed = composeProofs(blank, backwardStart, tail, { theorems: new Map(), relations: new Map() })
    const thm: Theorem = {
      name: 'blankToDoubleCut',
      lhs: mkDiagramWithBoundary(blank, []),
      rhs: mkDiagramWithBoundary(goal, []),
      steps: composed,
    }
    expect(() => checkTheorem(thm, { theorems: new Map(), relations: new Map() })).not.toThrow()
  })
})

describe('end to end: derived rule proved, stored, loaded, applied natively', () => {
  function dropQ(): Theorem {
    const l = new DiagramBuilder()
    const lp = l.termNode(l.root, p('\\a. a'))
    const lq = l.termNode(l.root, p('\\a. \\b. a'))
    const lb = l.wire(l.root, [
      { node: lp, port: { kind: 'output' } },
      { node: lq, port: { kind: 'output' } },
    ])
    const lhs = mkDiagramWithBoundary(l.build(), [lb])
    const r = new DiagramBuilder()
    const rp = r.termNode(r.root, p('\\a. a'))
    const rb = r.wire(r.root, [{ node: rp, port: { kind: 'output' } }])
    const rhs = mkDiagramWithBoundary(r.build(), [rb])
    return {
      name: 'dropQ', lhs, rhs,
      steps: [{ rule: 'erasure', sel: { region: lhs.diagram.root, regions: [], nodes: [lq], wires: [] } }],
    }
  }

  it('save → load → apply in a host through a proof step', () => {
    const theory: Theory = { relations: {}, theorems: [dropQ()] }
    const { ctx } = loadTheory(JSON.parse(JSON.stringify(theoryToJson(theory))))

    const h = new DiagramBuilder()
    const hp = h.termNode(h.root, p('\\a. a'))
    const hq = h.termNode(h.root, p('\\a. \\b. a'))
    const hub = h.termNode(h.root, p('y'))
    const v = h.wire(h.root, [
      { node: hp, port: { kind: 'output' } },
      { node: hq, port: { kind: 'output' } },
      { node: hub, port: { kind: 'freeVar', name: 'y' } },
    ])
    const d = h.build()
    const out = replayProof(d, [{
      rule: 'theorem', name: 'dropQ',
      at: { sel: { region: d.root, regions: [], nodes: [hp, hq], wires: [] }, args: [v] },
      direction: 'forward',
    }], ctx)
    // one application, regardless of the stored proof's length: hub + one P node
    expect(Object.values(out.nodes)).toHaveLength(2)
    expect(out.wires[v]?.endpoints).toHaveLength(2)
  })

  it('the whole pipeline preserves verification: tampered files are refused', () => {
    const theory: Theory = { relations: {}, theorems: [dropQ()] }
    const j = JSON.parse(JSON.stringify(theoryToJson(theory))) as { theorems: { steps: unknown[] }[] }
    j.theorems[0]!.steps = [] // tamper: claim the theorem with no proof
    expect(() => loadTheory(j)).toThrowError(/does not arrive at the stated right-hand side/)
  })

  it('verifyTheory + fingerprints: applying a theorem equals replaying its expansion', () => {
    const t = dropQ()
    const ctx = verifyTheory({ relations: {}, theorems: [t] })
    const h = new DiagramBuilder()
    const hp = h.termNode(h.root, p('\\a. a'))
    const hq = h.termNode(h.root, p('\\a. \\b. a'))
    const v = h.wire(h.root, [
      { node: hp, port: { kind: 'output' } },
      { node: hq, port: { kind: 'output' } },
    ])
    const d = h.build()
    const native = replayProof(d, [{
      rule: 'theorem', name: 'dropQ',
      at: { sel: { region: d.root, regions: [], nodes: [hp, hq], wires: [] }, args: [v] },
      direction: 'forward',
    }], ctx)
    // the same logical move done primitively: erase hq
    const primitive = replayProof(d, [{
      rule: 'erasure', sel: { region: d.root, regions: [], nodes: [hq], wires: [] },
    }], ctx)
    expect(diagramFingerprint(native)).toBe(diagramFingerprint(primitive))
  })
})
