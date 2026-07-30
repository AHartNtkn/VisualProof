import type {
  NodeId,
  RegionId,
  WireId,
} from '../kernel/diagram/diagram'
import { IOTA, relSig } from '../kernel/diagram/sig'
import {
  registerTheorem,
  verifyTheory,
  type ProofContext,
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
  quantifierScope,
} from './graph'
import {
  PrimitiveStepRecorder,
  onlyNewCut,
  onlyNewNode,
  onlyNewWire,
} from './record'
import {
  deiterationStep,
  directCuts,
  directNodes,
  endpointWire,
  exactOne,
  nodeWithHead,
  relationWire,
  scopedWires,
} from './arithmetic-support'
import type { ArithmeticStatements } from './statements'

const UNARY = relSig([IOTA])
const TERNARY = relSig([IOTA, IOTA, IOTA])

function exactHypothesesContent() {
  let graph = emptyGraph()
  const zero = declareWire(graph, graph.root, UNARY)
  graph = zero.graph
  const plus = declareWire(graph, graph.root, TERNARY)
  graph = plus.graph

  const baseVariables = quantifierScope(
    graph,
    graph.root,
    'forall',
    [IOTA, IOTA],
  )
  graph = baseVariables.graph
  const [zeroValue, right] = baseVariables.value.variables
  const baseClaim = implication(graph, baseVariables.value.body)
  graph = baseClaim.graph
  graph = atom(
    graph,
    baseClaim.value.antecedent,
    zero.value,
    [zeroValue!],
  ).graph
  graph = atom(
    graph,
    baseClaim.value.consequent,
    plus.value,
    [zeroValue!, right!, right!],
  ).graph

  const functionalVariables = quantifierScope(
    graph,
    graph.root,
    'forall',
    [IOTA, IOTA, IOTA, IOTA],
  )
  graph = functionalVariables.graph
  const [left, functionalRight, first, second] =
    functionalVariables.value.variables
  const functionalClaim = implication(
    graph,
    functionalVariables.value.body,
  )
  graph = functionalClaim.graph
  graph = atom(
    graph,
    functionalClaim.value.antecedent,
    plus.value,
    [left!, functionalRight!, first!],
  ).graph
  graph = atom(
    graph,
    functionalClaim.value.antecedent,
    plus.value,
    [left!, functionalRight!, second!],
  ).graph
  graph = identity(
    graph,
    functionalClaim.value.consequent,
    [first!, second!],
  ).graph

  return finishDiagramWithBoundary(graph, [zero.value, plus.value])
}

function plusLeftUnit(
  statements: ArithmeticStatements,
  context: ProofContext,
): Theorem {
  const lhs = finishDiagramWithBoundary(emptyGraph(), [])
  const forward = new PrimitiveStepRecorder(lhs.diagram, context)
  let before = forward.diagram

  forward.record('open zero/plus primitive universal scope', {
    rule: 'doubleCutIntro',
    sel: { region: forward.diagram.root, regions: [], nodes: [], wires: [] },
  })
  const primitiveScope = onlyNewCut(
    before,
    forward.diagram,
    forward.diagram.root,
  )
  const primitiveBody = exactOne(
    directCuts(forward.diagram, primitiveScope),
    'primitive body',
  )

  before = forward.diagram
  forward.record('introduce theorem-local zero relation', {
    rule: 'vacuousIntro',
    scope: primitiveScope,
    sig: UNARY,
  })
  const zero = onlyNewWire(before, forward.diagram, primitiveScope)

  before = forward.diagram
  forward.record('introduce theorem-local addition relation', {
    rule: 'vacuousIntro',
    scope: primitiveScope,
    sig: TERNARY,
  })
  const plus = onlyNewWire(before, forward.diagram, primitiveScope)

  before = forward.diagram
  forward.record('open exact-hypothesis implication', {
    rule: 'doubleCutIntro',
    sel: { region: primitiveBody, regions: [], nodes: [], wires: [] },
  })
  const hypotheses = onlyNewCut(before, forward.diagram, primitiveBody)
  const conclusion = exactOne(
    directCuts(forward.diagram, hypotheses),
    'conclusion',
  )

  before = forward.diagram
  forward.record('introduce temporary exact hypotheses handle', {
    rule: 'vacuousIntro',
    scope: hypotheses,
    sig: relSig([]),
  })
  const temporaryHypotheses = onlyNewWire(
    before,
    forward.diagram,
    hypotheses,
  )
  forward.record('assert temporary exact hypotheses handle', {
    rule: 'atomSpawn',
    region: hypotheses,
    wire: temporaryHypotheses,
  })
  forward.recordRelationJoin('ground exact plusBase and plusSingleValued hypotheses', {
    wire: temporaryHypotheses,
      content: exactHypothesesContent(),
      parameters: [zero, plus],
  })

  before = forward.diagram
  forward.record('open left-unit universal scope', {
    rule: 'doubleCutIntro',
    sel: { region: conclusion, regions: [], nodes: [], wires: [] },
  })
  const claimScope = onlyNewCut(before, forward.diagram, conclusion)
  const claimBody = exactOne(
    directCuts(forward.diagram, claimScope),
    'claim body',
  )

  const claimVariables: WireId[] = []
  for (const name of ['zero value', 'addend', 'output']) {
    before = forward.diagram
    forward.record(`introduce left-unit ${name}`, {
      rule: 'vacuousIntro',
      scope: claimScope,
      sig: IOTA,
    })
    claimVariables.push(onlyNewWire(before, forward.diagram, claimScope))
  }
  const [claimZero, claimAddend, claimOutput] = claimVariables as [
    WireId,
    WireId,
    WireId,
  ]

  before = forward.diagram
  forward.record('open left-unit implication', {
    rule: 'doubleCutIntro',
    sel: { region: claimBody, regions: [], nodes: [], wires: [] },
  })
  const claimAntecedent = onlyNewCut(
    before,
    forward.diagram,
    claimBody,
  )
  const claimConsequent = exactOne(
    directCuts(forward.diagram, claimAntecedent),
    'claim consequent',
  )

  function spawn(
    region: RegionId,
    head: WireId,
    args: readonly WireId[],
    label: string,
  ): NodeId {
    const prior = forward.diagram
    forward.record(`insert ${label}`, {
      rule: 'atomSpawn',
      region,
      wire: head,
    })
    const node = onlyNewNode(prior, forward.diagram, region)
    args.forEach((wire, index) => {
      forward.record(`attach ${label} argument ${index}`, {
        rule: 'wireJoin',
        input: {
          a: wire,
          b: endpointWire(forward.diagram, node, 'arg', index),
        },
      })
    })
    return node
  }

  spawn(
    claimAntecedent,
    zero,
    [claimZero],
    'left-unit zero premise',
  )
  spawn(
    claimAntecedent,
    plus,
    [claimZero, claimAddend, claimOutput],
    'left-unit addition premise',
  )
  spawn(
    claimAntecedent,
    plus,
    [claimZero, claimAddend, claimAddend],
    'specialized addition-base result',
  )

  before = forward.diagram
  forward.record('insert specialized functional-addition equality', {
    rule: 'identityInsert',
    region: claimAntecedent,
    wires: [claimOutput, claimAddend],
  })
  const equality = onlyNewNode(
    before,
    forward.diagram,
    claimAntecedent,
  )
  forward.record('iterate equality to left-unit goal', {
    rule: 'iteration',
    sel: {
      region: claimAntecedent,
      regions: [],
      nodes: [equality],
      wires: [],
    },
    target: claimConsequent,
    retargets: [],
  })

  const rhs = statements.plusLeftUnit
  const backward = new PrimitiveStepRecorder(
    rhs.diagram,
    context,
    'backward',
  )
  const reviewedPrimitiveScope = exactOne(
    directCuts(backward.diagram, backward.diagram.root),
    'reviewed primitive scope',
  )
  const reviewedPrimitiveBody = exactOne(
    directCuts(backward.diagram, reviewedPrimitiveScope),
    'reviewed primitive body',
  )
  const reviewedHypotheses = exactOne(
    directCuts(backward.diagram, reviewedPrimitiveBody),
    'reviewed hypotheses',
  )
  const children = directCuts(backward.diagram, reviewedHypotheses)
  const additionBase = exactOne(
    children.filter((region) =>
      scopedWires(backward.diagram, region).length === 2),
    'plusBase universal scope',
  )
  const additionFunctional = exactOne(
    children.filter((region) =>
      scopedWires(backward.diagram, region).length === 4),
    'plusSingleValued universal scope',
  )
  const reviewedConclusion = exactOne(
    children.filter((region) =>
      scopedWires(backward.diagram, region).length === 0),
    'reviewed theorem conclusion',
  )
  const reviewedZero = relationWire(
    backward.diagram,
    reviewedPrimitiveScope,
    UNARY,
  )
  const reviewedPlus = relationWire(
    backward.diagram,
    reviewedPrimitiveScope,
    TERNARY,
  )
  const reviewedClaimScope = exactOne(
    directCuts(backward.diagram, reviewedConclusion),
    'reviewed claim scope',
  )
  const reviewedClaimBody = exactOne(
    directCuts(backward.diagram, reviewedClaimScope),
    'reviewed claim body',
  )
  const reviewedClaimAntecedent = exactOne(
    directCuts(backward.diagram, reviewedClaimBody),
    'reviewed claim antecedent',
  )
  const reviewedClaimZeroNode = nodeWithHead(
    backward.diagram,
    reviewedClaimAntecedent,
    reviewedZero,
  )
  const reviewedClaimPlusNode = nodeWithHead(
    backward.diagram,
    reviewedClaimAntecedent,
    reviewedPlus,
  )
  const reviewedClaimZero = endpointWire(
    backward.diagram,
    reviewedClaimZeroNode,
    'arg',
    0,
  )
  const reviewedClaimAddend = endpointWire(
    backward.diagram,
    reviewedClaimPlusNode,
    'arg',
    1,
  )
  const reviewedClaimOutput = endpointWire(
    backward.diagram,
    reviewedClaimPlusNode,
    'arg',
    2,
  )

  before = backward.diagram
  backward.record('copy plusBase into left-unit antecedent', {
    rule: 'iteration',
    sel: {
      region: reviewedHypotheses,
      regions: [additionBase],
      nodes: [],
      wires: [],
    },
    target: reviewedClaimAntecedent,
    retargets: [],
  })
  const copiedBaseScope = onlyNewCut(
    before,
    backward.diagram,
    reviewedClaimAntecedent,
  )
  const copiedBaseBody = exactOne(
    directCuts(backward.diagram, copiedBaseScope),
    'copied base body',
  )
  const copiedBaseAntecedent = exactOne(
    directCuts(backward.diagram, copiedBaseBody),
    'copied base antecedent',
  )
  const copiedBaseConsequent = exactOne(
    directCuts(backward.diagram, copiedBaseAntecedent),
    'copied base consequent',
  )
  const copiedBaseZeroNode = nodeWithHead(
    backward.diagram,
    copiedBaseAntecedent,
    reviewedZero,
  )
  const copiedBasePlusNode = nodeWithHead(
    backward.diagram,
    copiedBaseConsequent,
    reviewedPlus,
  )
  backward.record('specialize plusBase zero variable', {
    rule: 'wireJoin',
    input: {
      a: reviewedClaimZero,
      b: endpointWire(
        backward.diagram,
        copiedBaseZeroNode,
        'arg',
        0,
      ),
    },
  })
  backward.record('specialize plusBase addend variable', {
    rule: 'wireJoin',
    input: {
      a: reviewedClaimAddend,
      b: endpointWire(
        backward.diagram,
        copiedBasePlusNode,
        'arg',
        1,
      ),
    },
  })
  backward.record(
    'discharge copied plusBase zero premise',
    deiterationStep(
      backward.diagram,
      copiedBaseAntecedent,
      copiedBaseZeroNode,
    ),
  )
  backward.record('expose specialized plusBase result', {
    rule: 'doubleCutElim',
    region: copiedBaseAntecedent,
  })
  backward.record('finish plusBase specialization', {
    rule: 'doubleCutElim',
    region: copiedBaseScope,
  })

  before = backward.diagram
  backward.record('copy plusSingleValued into left-unit antecedent', {
    rule: 'iteration',
    sel: {
      region: reviewedHypotheses,
      regions: [additionFunctional],
      nodes: [],
      wires: [],
    },
    target: reviewedClaimAntecedent,
    retargets: [],
  })
  const copiedFunctionalScope = onlyNewCut(
    before,
    backward.diagram,
    reviewedClaimAntecedent,
  )
  const copiedFunctionalBody = exactOne(
    directCuts(backward.diagram, copiedFunctionalScope),
    'copied functional body',
  )
  const copiedFunctionalAntecedent = exactOne(
    directCuts(backward.diagram, copiedFunctionalBody),
    'copied functional antecedent',
  )
  const copiedFunctionalConsequent = exactOne(
    directCuts(backward.diagram, copiedFunctionalAntecedent),
    'copied functional consequent',
  )
  const copiedPluses = directNodes(
    backward.diagram,
    copiedFunctionalAntecedent,
  ).filter((node) =>
    endpointWire(backward.diagram, node, 'head') === reviewedPlus)
  if (copiedPluses.length !== 2) {
    throw new Error(`expected two copied Plus premises, found ${copiedPluses.length}`)
  }
  const [firstPlus, secondPlus] = copiedPluses as [NodeId, NodeId]
  const copiedEquality = exactOne(
    directNodes(backward.diagram, copiedFunctionalConsequent),
    'copied functional equality',
  )

  backward.record('specialize plusSingleValued left variable', {
    rule: 'wireJoin',
    input: {
      a: reviewedClaimZero,
      b: endpointWire(backward.diagram, firstPlus, 'arg', 0),
    },
  })
  backward.record('specialize plusSingleValued right variable', {
    rule: 'wireJoin',
    input: {
      a: reviewedClaimAddend,
      b: endpointWire(backward.diagram, firstPlus, 'arg', 1),
    },
  })
  backward.record('specialize plusSingleValued first output', {
    rule: 'wireJoin',
    input: {
      a: reviewedClaimOutput,
      b: endpointWire(backward.diagram, firstPlus, 'arg', 2),
    },
  })
  backward.record('specialize plusSingleValued second output', {
    rule: 'wireJoin',
    input: {
      a: reviewedClaimAddend,
      b: endpointWire(backward.diagram, secondPlus, 'arg', 2),
    },
  })
  backward.record(
    'discharge copied supplied addition result',
    deiterationStep(
      backward.diagram,
      copiedFunctionalAntecedent,
      firstPlus,
    ),
  )
  backward.record(
    'discharge copied plusBase result',
    deiterationStep(
      backward.diagram,
      copiedFunctionalAntecedent,
      secondPlus,
    ),
  )
  backward.record('expose plusSingleValued equality', {
    rule: 'doubleCutElim',
    region: copiedFunctionalAntecedent,
  })
  backward.record('finish plusSingleValued specialization', {
    rule: 'doubleCutElim',
    region: copiedFunctionalScope,
  })
  if (backward.diagram.nodes[copiedEquality] === undefined) {
    throw new Error('specialized equality disappeared')
  }

  return {
    name: 'plusLeftUnit',
    lhs,
    rhs,
    actions: forward.actions,
    backActions: backward.actions,
  }
}

export function buildArithmeticBase(
  relations: Theory['relations'],
  prefix: readonly Theorem[],
  statements: ArithmeticStatements,
): readonly Theorem[] {
  let context = verifyTheory({ relations, theorems: prefix })
  const leftUnit = plusLeftUnit(statements, context)
  context = registerTheorem(context, leftUnit)
  void context
  return Object.freeze([leftUnit])
}
