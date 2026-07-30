import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { boundaryForm } from '../../../src/kernel/diagram/canonical/explore'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { singleStepAction } from '../../../src/kernel/proof/action'
import { verifyTheory } from '../../../src/kernel/proof/context'
import { applyStep, type ProofStep } from '../../../src/kernel/proof/step'
import { checkTheorem, type Theorem } from '../../../src/kernel/proof/theorem'
import { applyUnfold } from '../../../src/kernel/rules/fold'

function bodyR() {
  const builder = new DiagramBuilder()
  const predicate = builder.atom(builder.root, relSig([IOTA]))
  const argument = builder.wire(builder.root, [{
    node: predicate,
    port: { kind: 'arg', index: 0 },
  }])
  builder.atom(builder.root, relSig([]))
  return mkDiagramWithBoundary(builder.build(), [argument])
}

describe('folded-guard integration proof', () => {
  it('unfolds only a working copy while the ambient ref remains folded', () => {
    const definitions = new Map([['R', bodyR()]])
    const context = verifyTheory({
      relations: [...definitions],
      theorems: [],
    })
    const left = new DiagramBuilder()
    const ambient = left.ref(left.root, 'R', relSig([IOTA]))
    const argument = left.wire(left.root, [{
      node: ambient,
      port: { kind: 'arg', index: 0 },
    }])
    const lhs = mkDiagramWithBoundary(left.build(), [argument])

    const steps: ProofStep[] = []
    let current = lhs.diagram
    const iterate: ProofStep = {
      rule: 'iteration',
      sel: mkSelection(current, {
        region: current.root,
        regions: [],
        nodes: [ambient],
        wires: [],
      }),
      target: current.root,
      }
    current = applyStep(current, iterate, context)
    steps.push(iterate)
    expect(Object.values(current.nodes).filter((node) =>
      node.kind === 'ref')).toHaveLength(2)

    const copy = Object.entries(current.nodes).find(([id, node]) =>
      id !== ambient && node.kind === 'ref')![0]
    const unfold: ProofStep = { rule: 'unfold', nodeId: copy }
    current = applyStep(current, unfold, context)
    steps.push(unfold)
    expect(Object.values(current.nodes).filter((node) =>
      node.kind === 'ref')).toHaveLength(1)

    const conjunct = Object.entries(current.nodes).find(([, node]) =>
      node.kind === 'atom' && node.sig.args.length === 0)![0]
    const wrap: ProofStep = {
      rule: 'doubleCutIntro',
      sel: mkSelection(current, {
        region: current.root,
        regions: [],
        nodes: [conjunct],
        wires: [],
      }),
    }
    current = applyStep(current, wrap, context)
    steps.push(wrap)

    const rhs = mkDiagramWithBoundary(current, lhs.boundary)
    const theorem: Theorem = {
      name: 'foldedGuard',
      lhs,
      rhs,
      actions: steps.map((step) =>
        singleStepAction(step.rule, step)),
    }

    expect(() => checkTheorem(theorem, context)).not.toThrow()
    expect(Object.values(rhs.diagram.nodes).filter((node) =>
      node.kind === 'ref')).toHaveLength(1)

    const remainingRef = Object.entries(rhs.diagram.nodes).find(([, node]) =>
      node.kind === 'ref')![0]
    const fullyUnfolded = applyUnfold(
      rhs.diagram,
      remainingRef,
      definitions,
    )
    expect(boundaryForm(mkDiagramWithBoundary(
      fullyUnfolded,
      lhs.boundary,
    ))).not.toBe(boundaryForm(rhs))
    expect(Object.values(fullyUnfolded.nodes).some((node) =>
      node.kind === 'ref')).toBe(false)
  })
})
