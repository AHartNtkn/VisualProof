import type {
  Diagram,
  NodeId,
  RegionId,
} from '../kernel/diagram/diagram'
import { IOTA, relSig } from '../kernel/diagram/sig'
import {
  registerTheorem,
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
  onlyNewWire,
} from './record'

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
    retargets: [],
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
  ordinary: Theorem,
): Theorem {
  const blankGraph = emptyGraph()
  const lhs = finishDiagramWithBoundary(blankGraph, [])
  const relationContext = verifyTheory({ relations, theorems: [] })
  const context = registerTheorem(relationContext, ordinary)
  const recorder = new PrimitiveStepRecorder(lhs.diagram, context)

  let before = recorder.diagram
  recorder.record('reify blank as fresh P iff True', {
    rule: 'refSpawn',
    region: recorder.diagram.root,
    defId: 'truthReification',
    sig: relSig([PROPOSITION]),
  })
  const reification = onlyNewNode(
    before,
    recorder.diagram,
    recorder.diagram.root,
  )
  const p = onlyNewWire(
    before,
    recorder.diagram,
    recorder.diagram.root,
  )

  recorder.record('expose P iff True', {
    rule: 'unfold',
    nodeId: reification,
  })
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
  const originalWitness = exactlyOne(
    directNodes(recorder.diagram, reverseInner),
    'original witness occurrence',
  )

  before = recorder.diagram
  recorder.record('introduce pending proposition X in witness branch', {
    rule: 'vacuousIntro',
    scope: reverse,
    sig: PROPOSITION,
  })
  const x = onlyNewWire(before, recorder.diagram, reverse)

  before = recorder.diagram
  recorder.record('connect reified P to pending X', {
    rule: 'identityInsert',
    region: reverse,
    wires: [p, x],
  })
  const connection = onlyNewNode(before, recorder.diagram, reverse)

  recorder.record('iterate witness occurrence as X', {
    rule: 'iteration',
    sel: {
      region: reverseInner,
      regions: [],
      nodes: [originalWitness],
      wires: [],
    },
    target: reverseInner,
    retargets: [{
      boundary: 0,
      identity: connection,
      from: p,
      to: x,
    }],
  })

  recorder.record('discharge P-to-X connection', {
    rule: 'wireJoin',
    a: p,
    b: x,
  })
  recorder.record('expose original and substituted witnesses', {
    rule: 'doubleCutElim',
    region: reverse,
  })
  recorder.record('remove unused branch and original witness', {
    rule: 'erasure',
    sel: {
      region: recorder.diagram.root,
      regions: [forward],
      nodes: [originalWitness],
      wires: [],
    },
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
  const relationContext = verifyTheory({ relations, theorems: [] })
  const ordinaryContext = registerTheorem(relationContext, ordinary)
  const existence = existsProp(relations, ordinary)
  registerTheorem(ordinaryContext, existence)
  return Object.freeze([ordinary, existence])
}
