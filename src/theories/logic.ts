import type {
  Diagram,
  NodeId,
  RegionId,
} from '../kernel/diagram/diagram'
import { IOTA, relSig } from '../kernel/diagram/sig'
import {
  verifyTheory,
  type Theory,
} from '../kernel/proof/context'
import type { Theorem } from '../kernel/proof/theorem'
import {
  atom,
  declareWire,
  emptyGraph,
  finishDiagramWithBoundary,
  identity,
  implication,
} from './graph'
import {
  PrimitiveStepRecorder,
  onlyNewCut,
  onlyNewNode,
} from './record'
import {
  associativityInductionReification,
  commutativityInductionReification,
  relationIdentityReification,
  rightIdentityInductionReification,
  successorShiftInductionReification,
  truthReification,
} from './reification'

const PROPOSITION = relSig([])

function directCuts(
  diagram: Diagram,
  parent: RegionId,
): readonly RegionId[] {
  return Object.entries(diagram.regions)
    .filter(([, region]) =>
      region.kind === 'cut' && region.parent === parent)
    .map(([id]) => id)
    .sort()
}

function directNodes(
  diagram: Diagram,
  region: RegionId,
): readonly NodeId[] {
  return Object.entries(diagram.nodes)
    .filter(([, node]) => node.region === region)
    .map(([id]) => id)
    .sort()
}

function exactlyOne<T>(
  values: readonly T[],
  what: string,
): T {
  if (values.length !== 1) {
    throw new Error(`expected exactly one ${what}, found ${values.length}`)
  }
  return values[0]!
}

function ordinaryEqualityContradiction(
  relations: Theory['relations'],
): Theorem {
  let blank = emptyGraph()
  const leftWire = declareWire(blank, blank.root, IOTA)
  blank = leftWire.graph
  const rightWire = declareWire(blank, blank.root, IOTA)
  blank = rightWire.graph
  const lhs = finishDiagramWithBoundary(
    blank,
    [leftWire.value, rightWire.value],
  )
  const context = verifyTheory({ relations, theorems: [] })
  const recorder = new PrimitiveStepRecorder(
    lhs.diagram,
    context,
  )
  let before = recorder.diagram
  recorder.record('open law-of-noncontradiction cuts', {
    rule: 'doubleCutIntro',
    sel: {
      region: lhs.diagram.root,
      regions: [],
      nodes: [],
      wires: [],
    },
  })
  const enclosing = onlyNewCut(before, recorder.diagram, lhs.diagram.root)
  const disequality = onlyNewCut(before, recorder.diagram, enclosing)

  before = recorder.diagram
  recorder.record('insert the equality hypothesis', {
    rule: 'identityInsert',
    region: enclosing,
    wires: [leftWire.value, rightWire.value],
  })
  const equality = onlyNewNode(before, recorder.diagram, enclosing)
  recorder.record('iterate equality beneath the disequality cut', {
    rule: 'iteration',
    sel: {
      region: enclosing,
      regions: [],
      nodes: [equality],
      wires: [],
    },
    target: disequality,
  })

  let law = emptyGraph()
  const lawLeft = declareWire(law, law.root, IOTA)
  law = lawLeft.graph
  const lawRight = declareWire(law, law.root, IOTA)
  law = lawRight.graph
  const contradiction = implication(law, law.root)
  law = contradiction.graph
  law = identity(
    law,
    contradiction.value.antecedent,
    [lawLeft.value, lawRight.value],
  ).graph
  law = identity(
    law,
    contradiction.value.consequent,
    [lawLeft.value, lawRight.value],
  ).graph
  const rhs = finishDiagramWithBoundary(
    law,
    [lawLeft.value, lawRight.value],
  )

  return {
    name: 'ordinaryEqualityContradiction',
    lhs,
    rhs,
    actions: recorder.actions,
  }
}

function existsProp(
  relations: Theory['relations'],
  prior: readonly Theorem[],
): Theorem {
  const blankGraph = emptyGraph()
  const lhs = finishDiagramWithBoundary(blankGraph, [])
  const context = verifyTheory({ relations, theorems: prior })
  const recorder = new PrimitiveStepRecorder(lhs.diagram, context)

  let before = recorder.diagram
  recorder.record('cite truth reification at the blank sheet', {
    rule: 'theorem',
    name: 'truthReification',
    direction: 'forward',
    at: {
      sel: {
        region: recorder.diagram.root,
        regions: [],
        nodes: [],
        wires: [],
      },
      args: [],
    },
  })
  const citedWires = Object.keys(recorder.diagram.wires)
    .filter((wire) => before.wires[wire] === undefined)
  exactlyOne(citedWires, 'truth-reification witness')
  const rootBranches = directCuts(recorder.diagram, recorder.diagram.root)
  const forward = exactlyOne(
    rootBranches.filter((region) =>
      directNodes(recorder.diagram, region).length === 1),
    'P-to-True branch',
  )
  const reverse = exactlyOne(
    rootBranches.filter((region) => region !== forward),
    'True-to-P branch',
  )
  const reverseInner = exactlyOne(
    directCuts(recorder.diagram, reverse),
    'inner witness scope',
  )
  exactlyOne(
    directNodes(recorder.diagram, reverseInner),
    'truth-reification witness occurrence',
  )

  recorder.record('erase the vacuous P-to-True implication', {
    rule: 'erasure',
    sel: {
      region: recorder.diagram.root,
      regions: [forward],
      nodes: [],
      wires: [],
    },
  })
  recorder.record('eliminate the remaining True-to-P double cut', {
    rule: 'doubleCutElim',
    region: reverse,
  })

  let target = emptyGraph()
  const witness = declareWire(target, target.root, PROPOSITION)
  target = witness.graph
  target = atom(target, target.root, witness.value, []).graph
  const rhs = finishDiagramWithBoundary(target, [])

  return {
    name: 'existsProp',
    lhs,
    rhs,
    actions: recorder.actions,
  }
}

export function buildLogicalTheoremPrefix(
  relations: Theory['relations'],
): readonly Theorem[] {
  const ordinary = ordinaryEqualityContradiction(relations)
  const prefix = [
    ordinary,
    relationIdentityReification(),
    truthReification(),
    rightIdentityInductionReification(),
    associativityInductionReification(),
    successorShiftInductionReification(),
    commutativityInductionReification(),
  ]
  const existence = existsProp(relations, prefix)
  const completed = [...prefix, existence]
  verifyTheory({ relations, theorems: completed })
  return Object.freeze(completed)
}
