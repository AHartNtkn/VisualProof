import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { mkDiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { checkTheorem } from '../../src/kernel/proof/theorem'
import { verifyTheory } from '../../src/kernel/proof/store'
import { buildFregeTheory } from '../../src/theories/frege'
import { emptyDiagram, addTermNode, addCut } from '../../src/app/edit'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { startSession, applyForward, applyBackward, meet, assembleTheorem } from '../../src/app/session'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

describe('edit → prove → assemble, end to end', () => {
  it('a user-constructed goal is proven bidirectionally and checks', () => {
    const ctx = verifyTheory(buildFregeTheory())
    // EDIT: lhs = a single identity node; rhs = the same wrapped in two cuts
    const e0 = emptyDiagram()
    const { diagram: lhsD } = addTermNode(e0, e0.root, p('\\x. x'))
    const lhs = mkDiagramWithBoundary(lhsD, [])
    const r1 = addTermNode(e0, e0.root, p('\\x. x'))
    const selR = mkSelection(r1.diagram, { region: r1.diagram.root, regions: [], nodes: [r1.node], wires: [] })
    const r2 = addCut(r1.diagram, selR)
    const selR2 = mkSelection(r2.diagram, { region: r2.diagram.root, regions: [r2.region], nodes: [], wires: [] })
    const r3 = addCut(r2.diagram, selR2)
    const rhs = mkDiagramWithBoundary(r3.diagram, [])

    // PROVE: backward unwrap meets the untouched forward side
    let s = startSession(lhs, rhs, ctx)
    s = applyBackward(s, { kind: 'unDoubleCut', outer: r3.region })
    expect(meet(s)).toBe(true)
    const thm = assembleTheorem(s, 'identityDoubleCut')
    expect(() => checkTheorem(thm, ctx)).not.toThrow()
  })

  it('forward citation sessions check too', () => {
    const consts = new Set(['ZERO'])
    const ctx = verifyTheory(buildFregeTheory())
    const e0 = emptyDiagram()
    const { diagram: startD, node } = addTermNode(e0, e0.root, parseTerm('ZERO', consts))
    const wz = Object.entries(startD.wires).find(([, w]) =>
      w.endpoints.some((ep) => ep.node === node && ep.port.kind === 'output'))![0]
    const lhs = mkDiagramWithBoundary(startD, [wz])
    let s = startSession(lhs, lhs, ctx)
    s = applyForward(s, {
      rule: 'theorem', name: 'zeroIsNat', direction: 'forward',
      at: { sel: mkSelection(s.forward.current, { region: s.forward.current.root, regions: [], nodes: [node], wires: [] }), args: [wz] },
    })
    const rhs = mkDiagramWithBoundary(s.forward.current, [wz])
    const thm = { name: 'viaSession', lhs, rhs, steps: [...s.forward.steps] }
    expect(() => checkTheorem(thm, ctx)).not.toThrow()
  })
})
