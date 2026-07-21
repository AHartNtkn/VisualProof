import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { mkDiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { checkTheorem } from '../../src/kernel/proof/theorem'
import { verifyTheory } from '../../src/kernel/proof/store'
import { buildFregeTheory } from '../../src/theories/frege'
import { emptyDiagram, addCut } from '../../src/interaction/edit'
import { spawnTermNode } from '../../src/kernel/diagram/spawn'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { startSession, applyForward as applyForwardAction, applyBackward as applyBackwardAction, currentSide, meet, assembleTheorem, timelineActiveActions, type ProofSession } from '../../src/app/session'
import type { ProofStep } from '../../src/kernel/proof/step'
import { singleStepAction } from '../../src/kernel/proof/action'
import { bootFixture } from './boot-fixture'
import { adoptTheorem } from '../../src/app/session'
import { sessionTheory } from '../../src/app/persist'
import { loadTheory, theoryToJson } from '../../src/kernel/proof/store'

const p = (s: string) => parseTerm(s)
const gesture = (step: ProofStep) => singleStepAction(step.rule, step)
const applyForward = (session: ProofSession, step: ProofStep) => applyForwardAction(session, gesture(step))
const applyBackward = (session: ProofSession, step: ProofStep) => applyBackwardAction(session, gesture(step))

describe('edit → prove → assemble, end to end', () => {
  it('a user-constructed goal is proven bidirectionally and checks', () => {
    const ctx = verifyTheory(buildFregeTheory())
    // EDIT: lhs = a single identity node; rhs = the same wrapped in two cuts
    const e0 = emptyDiagram()
    const { diagram: lhsD } = spawnTermNode(e0, e0.root, p('\\x. x'))
    const lhs = mkDiagramWithBoundary(lhsD, [])
    const r1 = spawnTermNode(e0, e0.root, p('\\x. x'))
    const selR = mkSelection(r1.diagram, { region: r1.diagram.root, regions: [], nodes: [r1.node], wires: [] })
    const r2 = addCut(r1.diagram, selR)
    const selR2 = mkSelection(r2.diagram, { region: r2.diagram.root, regions: [r2.region], nodes: [], wires: [] })
    const r3 = addCut(r2.diagram, selR2)
    const rhs = mkDiagramWithBoundary(r3.diagram, [])

    // PROVE: backward unwrap meets the untouched forward side
    let s = startSession(lhs, rhs, ctx)
    s = applyBackward(s, { rule: 'doubleCutElim', region: r3.region })
    expect(meet(s)).toBe(true)
    const thm = assembleTheorem(s, 'identityDoubleCut')
    expect(() => checkTheorem(thm, ctx)).not.toThrow()
  })

  it('forward citation sessions check too', async () => {
    const { ctx } = await bootFixture()
    const e0 = emptyDiagram()
    const { diagram: startD, node } = spawnTermNode(e0, e0.root, p('(\\g. (\\x. g (x x)) (\\x. g (x x))) f'))
    const wo = Object.entries(startD.wires).find(([, w]) =>
      w.endpoints.some((ep) => ep.node === node && ep.port.kind === 'output'))![0]
    const wf = Object.entries(startD.wires).find(([, w]) =>
      w.endpoints.some((ep) => ep.node === node && ep.port.kind === 'freeVar'))![0]
    const lhs = mkDiagramWithBoundary(startD, [wo, wf])
    let s = startSession(lhs, lhs, ctx)
    s = applyForward(s, {
      rule: 'theorem', name: 'fixedPoint', direction: 'forward',
      at: { sel: mkSelection(currentSide(s, 'forward'), { region: currentSide(s, 'forward').root, regions: [], nodes: [node], wires: [] }), args: [wo, wf] },
    })
    const rhs = mkDiagramWithBoundary(currentSide(s, 'forward'), [wo, wf])
    const thm = { name: 'viaSession', lhs, rhs, actions: [...timelineActiveActions(s.forward)] }
    expect(() => checkTheorem(thm, ctx)).not.toThrow()
  })
})

describe('the full story: prove, adopt, save, reload, cite', () => {
  it('a session theorem survives the file road and is citable after reload', async () => {
    const boot = await bootFixture()
    // prove the toy double-cut theorem forward
    const l = emptyDiagram()
    const { diagram: lhsD } = spawnTermNode(l, l.root, p('\\x. x'))
    const lhs = mkDiagramWithBoundary(lhsD, [])
    let s = startSession(lhs, lhs, boot.ctx)
    s = applyForward(s, {
      rule: 'doubleCutIntro',
      sel: mkSelection(currentSide(s, 'forward'), { region: currentSide(s, 'forward').root, regions: [], nodes: [], wires: [] }),
    })
    const rhs = mkDiagramWithBoundary(currentSide(s, 'forward'), [])
    // test-level state surgery to make a met session without re-running
    s = {
      ...s,
      rhs,
      backward: { states: [rhs.diagram], boundaries: [rhs.boundary], actions: [], cursor: 0 },
    }
    const thm = assembleTheorem(s, 'wrapId')
    const s2 = adoptTheorem(s, thm)
    // save, reload, verify, cite
    const text = JSON.stringify(theoryToJson(sessionTheory(s2.ctx, { relations: boot.relations })))
    const { ctx } = loadTheory(JSON.parse(text))
    expect(ctx.theorems.has('wrapId')).toBe(true)
  })
})
