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
  let left = emptyGraph()
  const leftWire = declareWire(left, left.root, IOTA)
  left = leftWire.graph
  const rightWire = declareWire(left, left.root, IOTA)
  left = rightWire.graph
  const contradiction = implication(left, left.root)
  left = contradiction.graph
  left = identity(
    left,
    contradiction.value.antecedent,
    [leftWire.value, rightWire.value],
  ).graph
  left = identity(
    left,
    contradiction.value.consequent,
    [leftWire.value, rightWire.value],
  ).graph
  const lhs = finishDiagramWithBoundary(
    left,
    [leftWire.value, rightWire.value],
  )

  let right = emptyGraph()
  const rightLeft = declareWire(right, right.root, IOTA)
  right = rightLeft.graph
  const rightRight = declareWire(right, right.root, IOTA)
  right = rightRight.graph
  const rhs = finishDiagramWithBoundary(
    right,
    [rightLeft.value, rightRight.value],
  )
  const context = verifyTheory({ relations, theorems: [] })
  const recorder = new PrimitiveStepRecorder(
    rhs.diagram,
    context,
    'backward',
  )
  let before = recorder.diagram
  recorder.record('open equality contradiction cuts', {
    rule: 'doubleCutIntro',
    sel: {
      region: rhs.diagram.root,
      regions: [],
      nodes: [],
      wires: [],
    },
  })
  const enclosing = onlyNewCut(before, recorder.diagram, rhs.diagram.root)
  const disequality = onlyNewCut(before, recorder.diagram, enclosing)

  before = recorder.diagram
  recorder.record('insert the equality hypothesis', {
    rule: 'identityInsert',
    region: enclosing,
    wires: [rightLeft.value, rightRight.value],
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

  return {
    name: 'ordinaryEqualityContradiction',
    lhs,
    rhs,
    actions: [],
    backActions: recorder.actions,
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
  const inner = exactlyOne(
    directCuts(recorder.diagram, forward),
    'inner substitution scope',
  )
  const pOccurrence = exactlyOne(
    directNodes(recorder.diagram, forward),
    'reified P occurrence',
  )

  before = recorder.diagram
  recorder.record('introduce pending proposition X', {
    rule: 'vacuousIntro',
    scope: forward,
    sig: PROPOSITION,
  })
  const x = onlyNewWire(before, recorder.diagram, forward)

  before = recorder.diagram
  recorder.record('connect reified P to pending X', {
    rule: 'identityInsert',
    region: forward,
    wires: [p, x],
  })
  const connection = onlyNewNode(before, recorder.diagram, forward)

  before = recorder.diagram
  recorder.record('iterate connected P occurrence inward as X', {
    rule: 'iteration',
    sel: {
      region: forward,
      regions: [],
      nodes: [pOccurrence],
      wires: [],
    },
    target: inner,
    retargets: [{
      boundary: 0,
      identity: connection,
      from: p,
      to: x,
    }],
  })
  const innerX = onlyNewNode(before, recorder.diagram, inner)

  recorder.record('replace inner X occurrence with blank', {
    rule: 'erasure',
    sel: {
      region: inner,
      regions: [],
      nodes: [innerX],
      wires: [],
    },
  })
  recorder.record('remove spent biconditional and connection scaffold', {
    rule: 'erasure',
    sel: {
      region: recorder.diagram.root,
      regions: [forward],
      nodes: [],
      wires: [],
    },
  })
  recorder.record('remove final double cut around witness P', {
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
  const relationContext = verifyTheory({ relations, theorems: [] })
  const ordinaryContext = registerTheorem(relationContext, ordinary)
  const existence = existsProp(relations, ordinary)
  registerTheorem(ordinaryContext, existence)
  return Object.freeze([ordinary, existence])
}
