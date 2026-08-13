import type { NodeId, RegionId, WireId } from '../kernel/diagram/diagram'
import { IOTA, relSig } from '../kernel/diagram/sig'
import { findDeiterationEvidence } from '../kernel/rules/iteration'
import type { ProofContext } from '../kernel/proof/context'
import { bareWireAssembly } from '../kernel/rules/identity-rules'
import type { Theorem } from '../kernel/proof/theorem'
import {
  BINARY,
  TERNARY,
  UNARY,
  directCuts,
  directNodes,
  endpointWire,
  exactOne,
  relationWire,
  successorShiftCarrierContent,
  scopedWires,
} from './arithmetic-support'
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
import type { ArithmeticStatements } from './statements'

function successorSingleValuedContent() {
  let graph = emptyGraph()
  const successor = declareWire(graph, graph.root, BINARY)
  graph = successor.graph
  const variables = quantifierScope(
    graph,
    graph.root,
    'forall',
    [IOTA, IOTA, IOTA],
  )
  const [input, first, second] = variables.value.variables
  const claim = implication(variables.graph, variables.value.body)
  graph = atom(
    claim.graph,
    claim.value.antecedent,
    successor.value,
    [input!, first!],
  ).graph
  graph = atom(
    graph,
    claim.value.antecedent,
    successor.value,
    [input!, second!],
  ).graph
  graph = identity(
    graph,
    claim.value.consequent,
    [first!, second!],
  ).graph
  return finishDiagramWithBoundary(graph, [successor.value])
}

function deiterateNode(
  recorder: PrimitiveStepRecorder,
  label: string,
  region: RegionId,
  node: NodeId,
): void {
  const selection = {
    region,
    regions: [],
    nodes: [node],
    wires: [],
  } as const
  const evidence = findDeiterationEvidence(
    recorder.diagram,
    selection,
    65536,
  )
  recorder.record(label, {
    rule: 'deiteration',
    sel: selection,
    justifier: evidence.justifier,
    certificate: evidence.certificate,
  })
}

/**
 * The exact direct carrier E(a) combines:
 *   forall r, exists o, Plus(a,r,o)
 * with successor transport of the right input and output.
 *
 * This closed support theorem proves both its zero base and successor closure
 * from the ordinary standing arithmetic primitives. It deliberately owns no
 * reified property witness and contains no reference nodes.
 */
export function successorShiftCarrierInductive(
  statements: ArithmeticStatements,
  context: ProofContext,
): Theorem {
  const lhs = finishDiagramWithBoundary(emptyGraph(), [])
  const forward = new PrimitiveStepRecorder(lhs, context)

  forward.record('seed exact shift-support shell from associativity', {
    rule: 'theorem',
    name: 'plusAssoc',
    direction: 'forward',
    at: {
      sel: {
        region: forward.diagram.root,
        regions: [],
        nodes: [],
        wires: [],
      },
      args: [],
    },
  })
  const forwardPrimitiveScope = exactOne(
    directCuts(forward.diagram, forward.diagram.root),
    'carrier-support primitive scope',
  )
  const forwardPrimitiveBody = exactOne(
    directCuts(forward.diagram, forwardPrimitiveScope),
    'carrier-support primitive body',
  )
  const forwardHypotheses = exactOne(
    directCuts(forward.diagram, forwardPrimitiveBody),
    'carrier-support hypotheses',
  )
  const forwardConclusion = exactOne(
    directCuts(forward.diagram, forwardHypotheses).filter((region) =>
      scopedWires(forward.diagram, region).length === 0),
    'carrier-support conclusion',
  )
  const forwardZero = relationWire(
    forward.diagram,
    forwardPrimitiveScope,
    UNARY,
  )
  const forwardSuccessor = relationWire(
    forward.diagram,
    forwardPrimitiveScope,
    BINARY,
  )
  const forwardPlus = relationWire(
    forward.diagram,
    forwardPrimitiveScope,
    TERNARY,
  )
  const inheritedConclusion = directCuts(
    forward.diagram,
    forwardConclusion,
  )
  forward.record('erase inherited associativity conclusion', {
    rule: 'erasure',
    sel: {
      region: forwardConclusion,
      regions: inheritedConclusion,
      nodes: directNodes(forward.diagram, forwardConclusion),
      wires: [],
    },
  })

  const spawnForwardAtom = (
    label: string,
    region: RegionId,
    relation: WireId,
    args: readonly WireId[],
  ): NodeId => {
    const prior = forward.diagram
    forward.record(`spawn ${label}`, {
      rule: 'atomSpawn',
      region,
      wire: relation,
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

  let before = forward.diagram
  forward.record('introduce successorSingleValued hypothesis handle', {
    rule: 'vacuity',
    direction: 'insert',
    assembly: bareWireAssembly(
      'successorSingleValued',
      forwardHypotheses,
      relSig([]),
    ),
  })
  const forwardSuccessorFunctional = onlyNewWire(
    before,
    forward.diagram,
    forwardHypotheses,
  )
  forward.record('assert successorSingleValued hypothesis handle', {
    rule: 'atomSpawn',
    region: forwardHypotheses,
    wire: forwardSuccessorFunctional,
  })
  forward.recordRelationJoin('ground exact successorSingleValued hypothesis', {
    wire: forwardSuccessorFunctional,
      content: successorSingleValuedContent(),
      parameters: [forwardSuccessor],
  })

  const introduceForwardIndividuals = (
    scope: RegionId,
    labels: readonly string[],
  ): WireId[] => labels.map((label) => {
    const prior = forward.diagram
    forward.record(`introduce forward ${label}`, {
      rule: 'vacuity',
      direction: 'insert',
      assembly: bareWireAssembly('individual', scope, IOTA),
    })
    return onlyNewWire(prior, forward.diagram, scope)
  })
  const insertForwardIdentity = (
    label: string,
    region: RegionId,
    left: WireId,
    right: WireId,
  ): NodeId => {
    const prior = forward.diagram
    forward.record(`insert ${label}`, {
      rule: 'identityInsert',
      region,
      wires: [left, right],
    })
    return onlyNewNode(prior, forward.diagram, region)
  }

  before = forward.diagram
  forward.record('open forward shift carrier base scope', {
    rule: 'doubleCutIntro',
    sel: {
      region: forwardConclusion,
      regions: [],
      nodes: [],
      wires: [],
    },
  })
  const forwardBase = onlyNewCut(
    before,
    forward.diagram,
    forwardConclusion,
  )
  const forwardBaseBody = exactOne(
    directCuts(forward.diagram, forwardBase),
    'forward shift carrier base body',
  )
  const [forwardBaseValue] = introduceForwardIndividuals(
    forwardBase,
    ['shift carrier base value'],
  )
  before = forward.diagram
  forward.record('open forward shift carrier base implication', {
    rule: 'doubleCutIntro',
    sel: {
      region: forwardBaseBody,
      regions: [],
      nodes: [],
      wires: [],
    },
  })
  const forwardBaseAntecedent = onlyNewCut(
    before,
    forward.diagram,
    forwardBaseBody,
  )
  const forwardBaseConsequent = exactOne(
    directCuts(forward.diagram, forwardBaseAntecedent),
    'forward shift carrier base consequent',
  )
  spawnForwardAtom(
    'forward shift carrier base Zero',
    forwardBaseAntecedent,
    forwardZero,
    [forwardBaseValue!],
  )

  before = forward.diagram
  forward.record('open forward base totality scope', {
    rule: 'doubleCutIntro',
    sel: {
      region: forwardBaseConsequent,
      regions: [],
      nodes: [],
      wires: [],
    },
  })
  const forwardBaseTotality = onlyNewCut(
    before,
    forward.diagram,
    forwardBaseConsequent,
  )
  const [forwardBaseRight] = introduceForwardIndividuals(
    forwardBaseTotality,
    ['base totality right'],
  )
  spawnForwardAtom(
    'forward base totality evidence',
    forwardBaseTotality,
    forwardPlus,
    [forwardBaseValue!, forwardBaseRight!, forwardBaseRight!],
  )

  before = forward.diagram
  forward.record('open forward base transport scope', {
    rule: 'doubleCutIntro',
    sel: {
      region: forwardBaseConsequent,
      regions: [],
      nodes: [],
      wires: [],
    },
  })
  const forwardBaseTransport = onlyNewCut(
    before,
    forward.diagram,
    forwardBaseConsequent,
  )
  const [
    forwardBaseTransportRight,
    forwardBaseTransportRightSuccessor,
    forwardBaseTransportOutput,
    forwardBaseTransportOutputSuccessor,
  ] = introduceForwardIndividuals(
    forwardBaseTransport,
    [
      'base transport right',
      'base transport right successor',
      'base transport output',
      'base transport output successor',
    ],
  )
  const forwardBaseTransportBody = exactOne(
    directCuts(forward.diagram, forwardBaseTransport),
    'forward base transport body',
  )
  before = forward.diagram
  forward.record('open forward base transport implication', {
    rule: 'doubleCutIntro',
    sel: {
      region: forwardBaseTransportBody,
      regions: [],
      nodes: [],
      wires: [],
    },
  })
  const forwardBaseTransportAntecedent = onlyNewCut(
    before,
    forward.diagram,
    forwardBaseTransportBody,
  )
  spawnForwardAtom(
    'forward base transport right successor premise',
    forwardBaseTransportAntecedent,
    forwardSuccessor,
    [
      forwardBaseTransportRight!,
      forwardBaseTransportRightSuccessor!,
    ],
  )
  spawnForwardAtom(
    'forward base transport addition premise',
    forwardBaseTransportAntecedent,
    forwardPlus,
    [
      forwardBaseValue!,
      forwardBaseTransportRight!,
      forwardBaseTransportOutput!,
    ],
  )
  spawnForwardAtom(
    'forward base transport output successor premise',
    forwardBaseTransportAntecedent,
    forwardSuccessor,
    [
      forwardBaseTransportOutput!,
      forwardBaseTransportOutputSuccessor!,
    ],
  )
  spawnForwardAtom(
    'forward base transport canonical addition',
    forwardBaseTransportAntecedent,
    forwardPlus,
    [
      forwardBaseValue!,
      forwardBaseTransportRight!,
      forwardBaseTransportRight!,
    ],
  )
  insertForwardIdentity(
    'forward base transport output identity',
    forwardBaseTransportAntecedent,
    forwardBaseTransportOutput!,
    forwardBaseTransportRight!,
  )
  spawnForwardAtom(
    'forward base transport retargeted successor',
    forwardBaseTransportAntecedent,
    forwardSuccessor,
    [
      forwardBaseTransportOutput!,
      forwardBaseTransportRightSuccessor!,
    ],
  )
  insertForwardIdentity(
    'forward base transport successor identity',
    forwardBaseTransportAntecedent,
    forwardBaseTransportOutputSuccessor!,
    forwardBaseTransportRightSuccessor!,
  )
  spawnForwardAtom(
    'forward base transport successor addition',
    forwardBaseTransportAntecedent,
    forwardPlus,
    [
      forwardBaseValue!,
      forwardBaseTransportRightSuccessor!,
      forwardBaseTransportRightSuccessor!,
    ],
  )
  spawnForwardAtom(
    'forward base transport crossed successor addition',
    forwardBaseTransportAntecedent,
    forwardPlus,
    [
      forwardBaseValue!,
      forwardBaseTransportRightSuccessor!,
      forwardBaseTransportOutputSuccessor!,
    ],
  )

  before = forward.diagram
  forward.record('open forward carrier closure scope', {
    rule: 'doubleCutIntro',
    sel: {
      region: forwardConclusion,
      regions: [],
      nodes: [],
      wires: [],
    },
  })
  const forwardClosure = onlyNewCut(
    before,
    forward.diagram,
    forwardConclusion,
  )
  const forwardClosureBody = exactOne(
    directCuts(forward.diagram, forwardClosure),
    'forward carrier closure body',
  )
  const [forwardPredecessor, forwardSuccessorValue] =
    introduceForwardIndividuals(
      forwardClosure,
      ['closure predecessor', 'closure successor'],
    )
  before = forward.diagram
  forward.record('introduce temporary direct-E carrier', {
    rule: 'vacuity',
    direction: 'insert',
    assembly: bareWireAssembly('temporaryCarrier', forwardClosure, UNARY),
  })
  const temporaryCarrier = onlyNewWire(
    before,
    forward.diagram,
    forwardClosure,
  )
  before = forward.diagram
  forward.record('open forward carrier closure implication', {
    rule: 'doubleCutIntro',
    sel: {
      region: forwardClosureBody,
      regions: [],
      nodes: [],
      wires: [],
    },
  })
  const forwardClosureAntecedent = onlyNewCut(
    before,
    forward.diagram,
    forwardClosureBody,
  )
  const forwardClosureConsequent = exactOne(
    directCuts(forward.diagram, forwardClosureAntecedent),
    'forward carrier closure consequent',
  )
  spawnForwardAtom(
    'forward closure Succ premise',
    forwardClosureAntecedent,
    forwardSuccessor,
    [forwardPredecessor!, forwardSuccessorValue!],
  )
  spawnForwardAtom(
    'forward predecessor direct-E premise',
    forwardClosureAntecedent,
    temporaryCarrier,
    [forwardPredecessor!],
  )

  before = forward.diagram
  forward.record('open forward closure totality scope', {
    rule: 'doubleCutIntro',
    sel: {
      region: forwardClosureConsequent,
      regions: [],
      nodes: [],
      wires: [],
    },
  })
  const forwardClosureTotality = onlyNewCut(
    before,
    forward.diagram,
    forwardClosureConsequent,
  )
  const [
    forwardClosureRight,
    forwardClosurePredecessorOutput,
    forwardClosureSuccessorOutput,
  ] = introduceForwardIndividuals(
    forwardClosureTotality,
    [
      'closure totality right',
      'closure totality predecessor output',
      'closure totality successor output',
    ],
  )
  spawnForwardAtom(
    'forward closure inherited totality evidence',
    forwardClosureTotality,
    forwardPlus,
    [
      forwardPredecessor!,
      forwardClosureRight!,
      forwardClosurePredecessorOutput!,
    ],
  )
  spawnForwardAtom(
    'forward closure output successor evidence',
    forwardClosureTotality,
    forwardSuccessor,
    [
      forwardClosurePredecessorOutput!,
      forwardClosureSuccessorOutput!,
    ],
  )
  spawnForwardAtom(
    'forward closure stepped totality evidence',
    forwardClosureTotality,
    forwardPlus,
    [
      forwardSuccessorValue!,
      forwardClosureRight!,
      forwardClosureSuccessorOutput!,
    ],
  )

  before = forward.diagram
  forward.record('open forward closure transport scope', {
    rule: 'doubleCutIntro',
    sel: {
      region: forwardClosureConsequent,
      regions: [],
      nodes: [],
      wires: [],
    },
  })
  const forwardClosureTransport = onlyNewCut(
    before,
    forward.diagram,
    forwardClosureConsequent,
  )
  const [
    forwardTransportRight,
    forwardTransportRightSuccessor,
    forwardTransportOutput,
    forwardTransportOutputSuccessor,
  ] = introduceForwardIndividuals(
    forwardClosureTransport,
    [
      'closure transport right',
      'closure transport right successor',
      'closure transport output',
      'closure transport output successor',
    ],
  )
  const forwardClosureTransportBody = exactOne(
    directCuts(forward.diagram, forwardClosureTransport),
    'forward closure transport body',
  )
  before = forward.diagram
  forward.record('open forward closure transport implication', {
    rule: 'doubleCutIntro',
    sel: {
      region: forwardClosureTransportBody,
      regions: [],
      nodes: [],
      wires: [],
    },
  })
  const forwardClosureTransportAntecedent = onlyNewCut(
    before,
    forward.diagram,
    forwardClosureTransportBody,
  )
  const [
    forwardInheritedOutput,
    forwardInheritedOutputSuccessor,
  ] = introduceForwardIndividuals(
    forwardClosureTransportAntecedent,
    [
      'closure transport inherited output',
      'closure transport inherited output successor',
    ],
  )
  spawnForwardAtom(
    'forward closure transport right successor premise',
    forwardClosureTransportAntecedent,
    forwardSuccessor,
    [forwardTransportRight!, forwardTransportRightSuccessor!],
  )
  spawnForwardAtom(
    'forward closure transport addition premise',
    forwardClosureTransportAntecedent,
    forwardPlus,
    [
      forwardSuccessorValue!,
      forwardTransportRight!,
      forwardTransportOutput!,
    ],
  )
  spawnForwardAtom(
    'forward closure transport output successor premise',
    forwardClosureTransportAntecedent,
    forwardSuccessor,
    [forwardTransportOutput!, forwardTransportOutputSuccessor!],
  )
  spawnForwardAtom(
    'forward closure inherited addition',
    forwardClosureTransportAntecedent,
    forwardPlus,
    [
      forwardPredecessor!,
      forwardTransportRight!,
      forwardInheritedOutput!,
    ],
  )
  spawnForwardAtom(
    'forward closure inherited output successor',
    forwardClosureTransportAntecedent,
    forwardSuccessor,
    [forwardInheritedOutput!, forwardInheritedOutputSuccessor!],
  )
  spawnForwardAtom(
    'forward closure canonical successor addition',
    forwardClosureTransportAntecedent,
    forwardPlus,
    [
      forwardSuccessorValue!,
      forwardTransportRight!,
      forwardInheritedOutputSuccessor!,
    ],
  )
  // id(transport output, inherited output successor) has one outer wire
  // (the transport output), so the one-point collapse merges the inherited
  // successor into it on the spot; everything below uses the survivor.
  forward.record('insert forward closure transport output identity', {
    rule: 'identityInsert',
    region: forwardClosureTransportAntecedent,
    wires: [forwardTransportOutput!, forwardInheritedOutputSuccessor!],
  })
  spawnForwardAtom(
    'forward closure retargeted output successor',
    forwardClosureTransportAntecedent,
    forwardSuccessor,
    [
      forwardTransportOutput!,
      forwardTransportOutputSuccessor!,
    ],
  )
  spawnForwardAtom(
    'forward closure inherited shift result',
    forwardClosureTransportAntecedent,
    forwardPlus,
    [
      forwardPredecessor!,
      forwardTransportRightSuccessor!,
      forwardTransportOutput!,
    ],
  )
  spawnForwardAtom(
    'forward closure final shift result',
    forwardClosureTransportAntecedent,
    forwardPlus,
    [
      forwardSuccessorValue!,
      forwardTransportRightSuccessor!,
      forwardTransportOutputSuccessor!,
    ],
  )
  forward.recordRelationJoin('ground temporary carrier directly to E', {
    wire: temporaryCarrier,
      content: successorShiftCarrierContent(),
      parameters: [forwardSuccessor, forwardPlus],
  })

  const rhs = statements.successorShiftCarrierInductive
  const backward = new PrimitiveStepRecorder(rhs, context, 'backward')
  const primitiveScope = exactOne(
    directCuts(backward.diagram, backward.diagram.root),
    'reviewed carrier-support primitive scope',
  )
  const primitiveBody = exactOne(
    directCuts(backward.diagram, primitiveScope),
    'reviewed carrier-support primitive body',
  )
  const hypotheses = exactOne(
    directCuts(backward.diagram, primitiveBody),
    'reviewed carrier-support hypotheses',
  )
  const hypothesisChildren = directCuts(backward.diagram, hypotheses)
  const hypothesisByArity = (arity: number, label: string) => exactOne(
    hypothesisChildren.filter((region) =>
      scopedWires(backward.diagram, region).length === arity),
    label,
  )
  const conclusion = hypothesisByArity(0, 'carrier-support conclusion')
  const successorTotal = hypothesisByArity(
    1,
    'carrier-support successorTotal',
  )
  const additionBase = hypothesisByArity(2, 'carrier-support plusBase')
  const successorFunctional = hypothesisByArity(
    3,
    'carrier-support successorSingleValued',
  )
  const additionFunctional = hypothesisByArity(
    4,
    'carrier-support plusSingleValued',
  )
  const additionStep = hypothesisByArity(5, 'carrier-support plusStep')
  const zero = relationWire(backward.diagram, primitiveScope, UNARY)
  const successor = relationWire(backward.diagram, primitiveScope, BINARY)
  const plus = relationWire(backward.diagram, primitiveScope, TERNARY)

  const supportConditions = directCuts(backward.diagram, conclusion)
  const baseCondition = exactOne(
    supportConditions.filter((region) =>
      scopedWires(backward.diagram, region).length === 1),
    'carrier-support base condition',
  )
  const closureCondition = exactOne(
    supportConditions.filter((region) =>
      scopedWires(backward.diagram, region).length === 2),
    'carrier-support closure condition',
  )
  const baseConditionBody = exactOne(
    directCuts(backward.diagram, baseCondition),
    'carrier-support base body',
  )
  const baseConditionAntecedent = exactOne(
    directCuts(backward.diagram, baseConditionBody),
    'carrier-support base antecedent',
  )
  const baseConditionConsequent = exactOne(
    directCuts(backward.diagram, baseConditionAntecedent),
    'carrier-support base consequent',
  )
  const baseValue = exactOne(
    scopedWires(backward.diagram, baseCondition),
    'carrier-support base value',
  )
  const baseZero = exactOne(
    directNodes(backward.diagram, baseConditionAntecedent).filter((node) =>
      endpointWire(backward.diagram, node, 'head') === zero),
    'carrier-support base Zero',
  )
  const baseCarrierScopes = directCuts(
    backward.diagram,
    baseConditionConsequent,
  )
  const baseTotality = exactOne(
    baseCarrierScopes.filter((region) =>
      scopedWires(backward.diagram, region).length === 1),
    'carrier-support base totality scope',
  )
  const baseTransport = exactOne(
    baseCarrierScopes.filter((region) =>
      scopedWires(backward.diagram, region).length === 4),
    'carrier-support base transport scope',
  )
  const baseTotalityRight = exactOne(
    scopedWires(backward.diagram, baseTotality),
    'carrier-support base totality input',
  )
  const baseTotalityBody = exactOne(
    directCuts(backward.diagram, baseTotality),
    'carrier-support base totality body',
  )
  const baseTotalityGoal = exactOne(
    directNodes(backward.diagram, baseTotalityBody),
    'carrier-support base totality goal',
  )
  const baseTotalityOutput = endpointWire(
    backward.diagram,
    baseTotalityGoal,
    'arg',
    2,
  )
  before = backward.diagram
  backward.record('copy addition base into base totality scope', {
    rule: 'iteration',
    sel: {
      region: hypotheses,
      regions: [additionBase],
      nodes: [],
      wires: [],
    },
    target: baseTotality,
  })
  const copiedBaseScope = onlyNewCut(
    before,
    backward.diagram,
    baseTotality,
  )
  const copiedBaseBody = exactOne(
    directCuts(backward.diagram, copiedBaseScope),
    'copied base-totality addition-base body',
  )
  const copiedBaseAntecedent = exactOne(
    directCuts(backward.diagram, copiedBaseBody),
    'copied base-totality addition-base antecedent',
  )
  const copiedBaseConsequent = exactOne(
    directCuts(backward.diagram, copiedBaseAntecedent),
    'copied base-totality addition-base consequent',
  )
  const copiedBaseZero = exactOne(
    directNodes(backward.diagram, copiedBaseAntecedent),
    'copied base-totality Zero',
  )
  const copiedBaseResult = exactOne(
    directNodes(backward.diagram, copiedBaseConsequent),
    'copied base-totality Plus',
  )
  backward.record('specialize base-totality zero', {
    rule: 'wireJoin',
    input: {
      a: baseValue,
      b: endpointWire(backward.diagram, copiedBaseZero, 'arg', 0),
    },
  })
  backward.record('specialize base-totality right input', {
    rule: 'wireJoin',
    input: {
      a: baseTotalityRight,
      b: endpointWire(backward.diagram, copiedBaseResult, 'arg', 1),
    },
  })
  deiterateNode(
    backward,
    'discharge base-totality copied Zero',
    copiedBaseAntecedent,
    copiedBaseZero,
  )
  backward.record('expose base-totality addition-base result', {
    rule: 'doubleCutElim',
    region: copiedBaseAntecedent,
  })
  backward.record('finish base-totality addition-base specialization', {
    rule: 'doubleCutElim',
    region: copiedBaseScope,
  })
  backward.record('choose base totality input as its output', {
    rule: 'wireJoin',
    input: {
      a: baseTotalityRight,
      b: baseTotalityOutput,
    },
  })
  deiterateNode(
    backward,
    'discharge base totality goal',
    baseTotalityBody,
    baseTotalityGoal,
  )

  const baseTransportBody = exactOne(
    directCuts(backward.diagram, baseTransport),
    'carrier-support base transport body',
  )
  const baseTransportAntecedent = exactOne(
    directCuts(backward.diagram, baseTransportBody),
    'carrier-support base transport antecedent',
  )
  const baseTransportConsequent = exactOne(
    directCuts(backward.diagram, baseTransportAntecedent),
    'carrier-support base transport consequent',
  )
  const baseTransportPremises = directNodes(
    backward.diagram,
    baseTransportAntecedent,
  )
  const baseTransportPlus = exactOne(
    baseTransportPremises.filter((node) =>
      endpointWire(backward.diagram, node, 'head') === plus),
    'carrier-support base transport Plus premise',
  )
  const baseTransportSuccessors = baseTransportPremises.filter((node) =>
    endpointWire(backward.diagram, node, 'head') === successor)
  if (baseTransportSuccessors.length !== 2) {
    throw new Error(
      `expected two base transport successors, found ${baseTransportSuccessors.length}`,
    )
  }
  const baseRight = endpointWire(
    backward.diagram,
    baseTransportPlus,
    'arg',
    1,
  )
  const baseOutput = endpointWire(
    backward.diagram,
    baseTransportPlus,
    'arg',
    2,
  )
  const baseRightSuccessorNode = exactOne(
    baseTransportSuccessors.filter((node) =>
      endpointWire(backward.diagram, node, 'arg', 0) === baseRight),
    'carrier-support base right successor',
  )
  const baseOutputSuccessorNode = exactOne(
    baseTransportSuccessors.filter((node) =>
      endpointWire(backward.diagram, node, 'arg', 0) === baseOutput),
    'carrier-support base output successor',
  )
  const baseRightSuccessor = endpointWire(
    backward.diagram,
    baseRightSuccessorNode,
    'arg',
    1,
  )
  const baseOutputSuccessor = endpointWire(
    backward.diagram,
    baseOutputSuccessorNode,
    'arg',
    1,
  )
  const baseTransportGoal = exactOne(
    directNodes(backward.diagram, baseTransportConsequent),
    'carrier-support base transport goal',
  )

  const deriveBaseAddition = (
    right: WireId,
    label: string,
  ): NodeId => {
    const prior = backward.diagram
    backward.record(`copy addition base for ${label}`, {
      rule: 'iteration',
      sel: {
        region: hypotheses,
        regions: [additionBase],
        nodes: [],
        wires: [],
      },
      target: baseTransportAntecedent,
      })
    const scope = onlyNewCut(
      prior,
      backward.diagram,
      baseTransportAntecedent,
    )
    const body = exactOne(
      directCuts(backward.diagram, scope),
      `${label} addition-base body`,
    )
    const antecedent = exactOne(
      directCuts(backward.diagram, body),
      `${label} addition-base antecedent`,
    )
    const consequent = exactOne(
      directCuts(backward.diagram, antecedent),
      `${label} addition-base consequent`,
    )
    const zeroPremise = exactOne(
      directNodes(backward.diagram, antecedent),
      `${label} addition-base Zero`,
    )
    const result = exactOne(
      directNodes(backward.diagram, consequent),
      `${label} addition-base Plus`,
    )
    backward.record(`specialize ${label} addition-base zero`, {
      rule: 'wireJoin',
      input: {
        a: baseValue,
        b: endpointWire(backward.diagram, zeroPremise, 'arg', 0),
      },
    })
    backward.record(`specialize ${label} addition-base right`, {
      rule: 'wireJoin',
      input: {
        a: right,
        b: endpointWire(backward.diagram, result, 'arg', 1),
      },
    })
    deiterateNode(
      backward,
      `discharge ${label} addition-base Zero`,
      antecedent,
      zeroPremise,
    )
    backward.record(`expose ${label} addition-base result`, {
      rule: 'doubleCutElim',
      region: antecedent,
    })
    backward.record(`finish ${label} addition-base specialization`, {
      rule: 'doubleCutElim',
      region: scope,
    })
    return result
  }

  const baseAtRight = deriveBaseAddition(
    baseRight,
    'base-transport right',
  )
  const deriveBaseOutputIdentity = (): NodeId => {
    const prior = backward.diagram
    backward.record('copy addition functionality into base transport', {
      rule: 'iteration',
      sel: {
        region: hypotheses,
        regions: [additionFunctional],
        nodes: [],
        wires: [],
      },
      target: baseTransportAntecedent,
    })
    const copiedAdditionFunctional = onlyNewCut(
      prior,
      backward.diagram,
      baseTransportAntecedent,
    )
    const copiedAdditionFunctionalBody = exactOne(
      directCuts(backward.diagram, copiedAdditionFunctional),
      'base-transport addition-functionality body',
    )
    const copiedAdditionFunctionalAntecedent = exactOne(
      directCuts(backward.diagram, copiedAdditionFunctionalBody),
      'base-transport addition-functionality antecedent',
    )
    const copiedAdditionFunctionalConsequent = exactOne(
      directCuts(backward.diagram, copiedAdditionFunctionalAntecedent),
      'base-transport addition-functionality consequent',
    )
    const copiedFunctionalPluses = directNodes(
      backward.diagram,
      copiedAdditionFunctionalAntecedent,
    )
    if (copiedFunctionalPluses.length !== 2) {
      throw new Error(
        `expected two base-transport functional Plus premises, found ${copiedFunctionalPluses.length}`,
      )
    }
    const [functionalFirst, functionalSecond] = copiedFunctionalPluses
    for (const [label, outer, inner] of [
      [
        'left',
        baseValue,
        endpointWire(backward.diagram, functionalFirst!, 'arg', 0),
      ],
      [
        'right',
        baseRight,
        endpointWire(backward.diagram, functionalFirst!, 'arg', 1),
      ],
      [
        'actual output',
        baseOutput,
        endpointWire(backward.diagram, functionalFirst!, 'arg', 2),
      ],
      [
        'canonical output',
        baseRight,
        endpointWire(backward.diagram, functionalSecond!, 'arg', 2),
      ],
    ] as const) {
      backward.record(`specialize base-transport functionality ${label}`, {
        rule: 'wireJoin',
        input: { a: outer, b: inner },
      })
    }
    deiterateNode(
      backward,
      'discharge base-transport actual addition result',
      copiedAdditionFunctionalAntecedent,
      functionalFirst!,
    )
    deiterateNode(
      backward,
      'discharge base-transport canonical addition result',
      copiedAdditionFunctionalAntecedent,
      functionalSecond!,
    )
    const identity = exactOne(
      directNodes(backward.diagram, copiedAdditionFunctionalConsequent),
      'base-transport output identity',
    )
    backward.record('expose base-transport output identity', {
      rule: 'doubleCutElim',
      region: copiedAdditionFunctionalAntecedent,
    })
    backward.record('finish base-transport addition functionality', {
      rule: 'doubleCutElim',
      region: copiedAdditionFunctional,
    })
    return identity
  }
  const baseOutputIdentity = deriveBaseOutputIdentity()

  // Substitution is the derivation (no retargets): copy the right-successor
  // premise, then sever the base right so the one-point collapse lands the
  // copy's input on the base output through the output identity. That
  // consumes the identity; a second functionality pass restores it.
  before = backward.diagram
  backward.record('copy base right successor beside the output', {
    rule: 'iteration',
    sel: {
      region: baseTransportAntecedent,
      regions: [],
      nodes: [baseRightSuccessorNode],
      wires: [],
    },
    target: baseTransportAntecedent,
  })
  const transportedRightSuccessor = onlyNewNode(
    before,
    backward.diagram,
    baseTransportAntecedent,
  )
  if (backward.diagram.wires[baseRight]!.endpoints
    .filter((endpoint) => endpoint.node === transportedRightSuccessor)
    .length !== 1) {
    throw new Error('right-successor copy must touch the base right once')
  }
  backward.record('land the right-successor copy on the base output', {
    rule: 'wireSever',
    input: {
      wire: baseRight,
      keep: backward.diagram.wires[baseRight]!.endpoints
        .filter((endpoint) =>
          endpoint.node !== baseOutputIdentity
          && endpoint.node !== transportedRightSuccessor),
      scope: baseTransportAntecedent,
    },
  })
  deriveBaseOutputIdentity()

  const deriveBaseSuccessorIdentity = (): NodeId => {
    const prior = backward.diagram
    backward.record('copy successor functionality into base transport', {
      rule: 'iteration',
      sel: {
        region: hypotheses,
        regions: [successorFunctional],
        nodes: [],
        wires: [],
      },
      target: baseTransportAntecedent,
    })
    const copiedSuccessorFunctional = onlyNewCut(
      prior,
      backward.diagram,
      baseTransportAntecedent,
    )
    const copiedSuccessorFunctionalBody = exactOne(
      directCuts(backward.diagram, copiedSuccessorFunctional),
      'base-transport successor-functionality body',
    )
    const copiedSuccessorFunctionalAntecedent = exactOne(
      directCuts(backward.diagram, copiedSuccessorFunctionalBody),
      'base-transport successor-functionality antecedent',
    )
    const copiedSuccessorFunctionalConsequent = exactOne(
      directCuts(backward.diagram, copiedSuccessorFunctionalAntecedent),
      'base-transport successor-functionality consequent',
    )
    const copiedFunctionalSuccessors = directNodes(
      backward.diagram,
      copiedSuccessorFunctionalAntecedent,
    )
    if (copiedFunctionalSuccessors.length !== 2) {
      throw new Error(
        `expected two base-transport functional Succ premises, found ${copiedFunctionalSuccessors.length}`,
      )
    }
    const [functionalSuccessorFirst, functionalSuccessorSecond] =
      copiedFunctionalSuccessors
    for (const [label, outer, inner] of [
      [
        'input',
        baseOutput,
        endpointWire(
          backward.diagram,
          functionalSuccessorFirst!,
          'arg',
          0,
        ),
      ],
      [
        'actual output',
        baseOutputSuccessor,
        endpointWire(
          backward.diagram,
          functionalSuccessorFirst!,
          'arg',
          1,
        ),
      ],
      [
        'canonical output',
        baseRightSuccessor,
        endpointWire(
          backward.diagram,
          functionalSuccessorSecond!,
          'arg',
          1,
        ),
      ],
    ] as const) {
      backward.record(`specialize base successor functionality ${label}`, {
        rule: 'wireJoin',
        input: { a: outer, b: inner },
      })
    }
    deiterateNode(
      backward,
      'discharge base actual successor',
      copiedSuccessorFunctionalAntecedent,
      functionalSuccessorFirst!,
    )
    deiterateNode(
      backward,
      'discharge base transported successor',
      copiedSuccessorFunctionalAntecedent,
      functionalSuccessorSecond!,
    )
    const identity = exactOne(
      directNodes(backward.diagram, copiedSuccessorFunctionalConsequent),
      'base-transport successor identity',
    )
    backward.record('expose base-transport successor identity', {
      rule: 'doubleCutElim',
      region: copiedSuccessorFunctionalAntecedent,
    })
    backward.record('finish base-transport successor functionality', {
      rule: 'doubleCutElim',
      region: copiedSuccessorFunctional,
    })
    return identity
  }
  const baseSuccessorIdentity = deriveBaseSuccessorIdentity()

  const baseAtRightSuccessor = deriveBaseAddition(
    baseRightSuccessor,
    'base-transport right successor',
  )
  // Substitution is the derivation (no retargets): copy the right-successor
  // addition, sever the right successor so the one-point collapse lands the
  // copy's output on the output successor (consuming the successor
  // identity), discharge the goal against the copy, and restore the
  // identity with a second functionality pass.
  before = backward.diagram
  backward.record('copy right-successor addition for the shift goal', {
    rule: 'iteration',
    sel: {
      region: baseTransportAntecedent,
      regions: [],
      nodes: [baseAtRightSuccessor],
      wires: [],
    },
    target: baseTransportAntecedent,
  })
  const crossedBaseAddition = onlyNewNode(
    before,
    backward.diagram,
    baseTransportAntecedent,
  )
  backward.record('land the crossed addition on the output successor', {
    rule: 'wireSever',
    input: {
      wire: baseRightSuccessor,
      keep: backward.diagram.wires[baseRightSuccessor]!.endpoints
        .filter((endpoint) =>
          endpoint.node !== baseSuccessorIdentity
          && !(
            endpoint.node === crossedBaseAddition
            && endpoint.port.kind === 'arg'
            && endpoint.port.index === 2
          )),
      scope: baseTransportAntecedent,
    },
  })
  deiterateNode(
    backward,
    'discharge base successor-shift goal',
    baseTransportConsequent,
    baseTransportGoal,
  )
  deriveBaseSuccessorIdentity()

  void baseZero
  void baseAtRight
  void transportedRightSuccessor
  void baseAtRightSuccessor

  const closureBody = exactOne(
    directCuts(backward.diagram, closureCondition),
    'carrier-support closure body',
  )
  const closureAntecedent = exactOne(
    directCuts(backward.diagram, closureBody),
    'carrier-support closure antecedent',
  )
  const closureConsequent = exactOne(
    directCuts(backward.diagram, closureAntecedent).filter((region) =>
      scopedWires(backward.diagram, region).length === 0),
    'carrier-support closure consequent',
  )
  const [predecessor, successorValue] = scopedWires(
    backward.diagram,
    closureCondition,
  )
  if (predecessor === undefined || successorValue === undefined) {
    throw new Error('missing carrier-support closure variables')
  }
  const closureSuccessor = exactOne(
    directNodes(backward.diagram, closureAntecedent).filter((node) =>
      endpointWire(backward.diagram, node, 'head') === successor),
    'carrier-support closure Succ premise',
  )
  const predecessorCarrierScopes = directCuts(
    backward.diagram,
    closureAntecedent,
  ).filter((region) => region !== closureConsequent)
  const predecessorTotality = exactOne(
    predecessorCarrierScopes.filter((region) =>
      scopedWires(backward.diagram, region).length === 1),
    'carrier-support predecessor totality',
  )
  const predecessorTransport = exactOne(
    predecessorCarrierScopes.filter((region) =>
      scopedWires(backward.diagram, region).length === 4),
    'carrier-support predecessor transport',
  )
  const successorCarrierScopes = directCuts(
    backward.diagram,
    closureConsequent,
  )
  const successorTotalityScope = exactOne(
    successorCarrierScopes.filter((region) =>
      scopedWires(backward.diagram, region).length === 1),
    'carrier-support successor totality',
  )
  const successorTransport = exactOne(
    successorCarrierScopes.filter((region) =>
      scopedWires(backward.diagram, region).length === 4),
    'carrier-support successor transport',
  )
  const successorTotalityRight = exactOne(
    scopedWires(backward.diagram, successorTotalityScope),
    'carrier-support successor totality right input',
  )
  const successorTotalityBody = exactOne(
    directCuts(backward.diagram, successorTotalityScope),
    'carrier-support successor totality body',
  )
  const successorTotalityGoal = exactOne(
    directNodes(backward.diagram, successorTotalityBody),
    'carrier-support successor totality goal',
  )
  const successorTotalityOutput = endpointWire(
    backward.diagram,
    successorTotalityGoal,
    'arg',
    2,
  )

  before = backward.diagram
  backward.record('copy inherited totality into closure totality', {
    rule: 'iteration',
    sel: {
      region: closureAntecedent,
      regions: [predecessorTotality],
      nodes: [],
      wires: [],
    },
    target: successorTotalityScope,
  })
  const copiedInheritedTotality = onlyNewCut(
    before,
    backward.diagram,
    successorTotalityScope,
  )
  const copiedInheritedRight = exactOne(
    scopedWires(backward.diagram, copiedInheritedTotality),
    'copied inherited totality input',
  )
  backward.record('specialize inherited totality at closure right input', {
    rule: 'wireJoin',
    input: {
      a: successorTotalityRight,
      b: copiedInheritedRight,
    },
  })
  const copiedInheritedTotalityBody = exactOne(
    directCuts(backward.diagram, copiedInheritedTotality),
    'copied inherited totality body',
  )
  const inheritedAddition = exactOne(
    directNodes(backward.diagram, copiedInheritedTotalityBody),
    'copied inherited totality addition',
  )
  const predecessorOutput = endpointWire(
    backward.diagram,
    inheritedAddition,
    'arg',
    2,
  )
  backward.record('expose inherited totality witness', {
    rule: 'doubleCutElim',
    region: copiedInheritedTotality,
  })

  before = backward.diagram
  backward.record('copy successor totality into closure totality', {
    rule: 'iteration',
    sel: {
      region: hypotheses,
      regions: [successorTotal],
      nodes: [],
      wires: [],
    },
    target: successorTotalityScope,
  })
  const copiedSuccessorTotal = onlyNewCut(
    before,
    backward.diagram,
    successorTotalityScope,
  )
  const copiedSuccessorTotalBody = exactOne(
    directCuts(backward.diagram, copiedSuccessorTotal),
    'copied closure successor-totality body',
  )
  const outputSuccessor = exactOne(
    directNodes(backward.diagram, copiedSuccessorTotalBody),
    'copied closure output successor',
  )
  backward.record('specialize closure output successor input', {
    rule: 'wireJoin',
    input: {
      a: predecessorOutput,
      b: endpointWire(backward.diagram, outputSuccessor, 'arg', 0),
    },
  })
  const successorOutput = endpointWire(
    backward.diagram,
    outputSuccessor,
    'arg',
    1,
  )
  backward.record('expose closure output successor witness', {
    rule: 'doubleCutElim',
    region: copiedSuccessorTotal,
  })

  before = backward.diagram
  backward.record('copy addition step into closure totality', {
    rule: 'iteration',
    sel: {
      region: hypotheses,
      regions: [additionStep],
      nodes: [],
      wires: [],
    },
    target: successorTotalityScope,
  })
  const copiedTotalityStep = onlyNewCut(
    before,
    backward.diagram,
    successorTotalityScope,
  )
  const copiedTotalityStepBody = exactOne(
    directCuts(backward.diagram, copiedTotalityStep),
    'copied closure-totality step body',
  )
  const copiedTotalityStepAntecedent = exactOne(
    directCuts(backward.diagram, copiedTotalityStepBody),
    'copied closure-totality step antecedent',
  )
  const copiedTotalityStepConsequent = exactOne(
    directCuts(backward.diagram, copiedTotalityStepAntecedent),
    'copied closure-totality step consequent',
  )
  const copiedTotalityStepPremises = directNodes(
    backward.diagram,
    copiedTotalityStepAntecedent,
  )
  const copiedTotalityStepPlus = exactOne(
    copiedTotalityStepPremises.filter((node) =>
      endpointWire(backward.diagram, node, 'head') === plus),
    'copied closure-totality step Plus',
  )
  const copiedTotalityStepSuccessors = copiedTotalityStepPremises.filter(
    (node) => endpointWire(backward.diagram, node, 'head') === successor,
  )
  if (copiedTotalityStepSuccessors.length !== 2) {
    throw new Error(
      `expected two closure-totality step successors, found ${copiedTotalityStepSuccessors.length}`,
    )
  }
  const copiedTotalityStepResult = exactOne(
    directNodes(backward.diagram, copiedTotalityStepConsequent),
    'copied closure-totality step result',
  )
  const copiedTotalityLeft = endpointWire(
    backward.diagram,
    copiedTotalityStepPlus,
    'arg',
    0,
  )
  const copiedTotalityOutput = endpointWire(
    backward.diagram,
    copiedTotalityStepPlus,
    'arg',
    2,
  )
  const copiedTotalityLeftSuccessor = exactOne(
    copiedTotalityStepSuccessors.filter((node) =>
      endpointWire(backward.diagram, node, 'arg', 0)
        === copiedTotalityLeft),
    'copied closure-totality left successor',
  )
  const copiedTotalityOutputSuccessor = exactOne(
    copiedTotalityStepSuccessors.filter((node) =>
      endpointWire(backward.diagram, node, 'arg', 0)
        === copiedTotalityOutput),
    'copied closure-totality output successor',
  )
  for (const [label, outer, inner] of [
    ['left', predecessor, copiedTotalityLeft],
    [
      'right',
      successorTotalityRight,
      endpointWire(backward.diagram, copiedTotalityStepPlus, 'arg', 1),
    ],
    ['output', predecessorOutput, copiedTotalityOutput],
    [
      'left successor',
      successorValue,
      endpointWire(
        backward.diagram,
        copiedTotalityLeftSuccessor,
        'arg',
        1,
      ),
    ],
    [
      'output successor',
      successorOutput,
      endpointWire(
        backward.diagram,
        copiedTotalityOutputSuccessor,
        'arg',
        1,
      ),
    ],
  ] as const) {
    backward.record(`specialize closure-totality step ${label}`, {
      rule: 'wireJoin',
      input: { a: outer, b: inner },
    })
  }
  for (const node of [
    copiedTotalityStepPlus,
    copiedTotalityLeftSuccessor,
    copiedTotalityOutputSuccessor,
  ]) {
    deiterateNode(
      backward,
      'discharge closure-totality step premise',
      copiedTotalityStepAntecedent,
      node,
    )
  }
  backward.record('expose closure-totality step result', {
    rule: 'doubleCutElim',
    region: copiedTotalityStepAntecedent,
  })
  backward.record('finish closure-totality step specialization', {
    rule: 'doubleCutElim',
    region: copiedTotalityStep,
  })
  backward.record('choose closure totality successor output', {
    rule: 'wireJoin',
    input: {
      a: successorOutput,
      b: successorTotalityOutput,
    },
  })
  deiterateNode(
    backward,
    'discharge closure totality goal',
    successorTotalityBody,
    successorTotalityGoal,
  )

  void predecessorTransport
  void copiedTotalityStepResult
  void closureSuccessor

  const successorTransportBody = exactOne(
    directCuts(backward.diagram, successorTransport),
    'carrier-support successor transport body',
  )
  const successorTransportAntecedent = exactOne(
    directCuts(backward.diagram, successorTransportBody),
    'carrier-support successor transport antecedent',
  )
  const successorTransportConsequent = exactOne(
    directCuts(backward.diagram, successorTransportAntecedent),
    'carrier-support successor transport consequent',
  )
  const successorTransportPremises = directNodes(
    backward.diagram,
    successorTransportAntecedent,
  )
  const successorTransportPlus = exactOne(
    successorTransportPremises.filter((node) =>
      endpointWire(backward.diagram, node, 'head') === plus),
    'carrier-support successor transport Plus premise',
  )
  const successorTransportSuccessors = successorTransportPremises.filter(
    (node) => endpointWire(backward.diagram, node, 'head') === successor,
  )
  if (successorTransportSuccessors.length !== 2) {
    throw new Error(
      `expected two successor transport Succ premises, found ${successorTransportSuccessors.length}`,
    )
  }
  const closureRight = endpointWire(
    backward.diagram,
    successorTransportPlus,
    'arg',
    1,
  )
  const closureOutput = endpointWire(
    backward.diagram,
    successorTransportPlus,
    'arg',
    2,
  )
  const closureRightSuccessorNode = exactOne(
    successorTransportSuccessors.filter((node) =>
      endpointWire(backward.diagram, node, 'arg', 0) === closureRight),
    'carrier-support closure right successor',
  )
  const closureOutputSuccessorNode = exactOne(
    successorTransportSuccessors.filter((node) =>
      endpointWire(backward.diagram, node, 'arg', 0) === closureOutput),
    'carrier-support closure output successor',
  )
  const closureRightSuccessor = endpointWire(
    backward.diagram,
    closureRightSuccessorNode,
    'arg',
    1,
  )
  const closureOutputSuccessor = endpointWire(
    backward.diagram,
    closureOutputSuccessorNode,
    'arg',
    1,
  )
  const successorTransportGoal = exactOne(
    directNodes(backward.diagram, successorTransportConsequent),
    'carrier-support successor transport goal',
  )

  before = backward.diagram
  backward.record('copy inherited totality into successor transport', {
    rule: 'iteration',
    sel: {
      region: closureAntecedent,
      regions: [predecessorTotality],
      nodes: [],
      wires: [],
    },
    target: successorTransportAntecedent,
  })
  const copiedTransportTotality = onlyNewCut(
    before,
    backward.diagram,
    successorTransportAntecedent,
  )
  const copiedTransportRight = exactOne(
    scopedWires(backward.diagram, copiedTransportTotality),
    'copied successor-transport inherited totality input',
  )
  backward.record('specialize inherited totality at transport right', {
    rule: 'wireJoin',
    input: {
      a: closureRight,
      b: copiedTransportRight,
    },
  })
  const copiedTransportTotalityBody = exactOne(
    directCuts(backward.diagram, copiedTransportTotality),
    'copied successor-transport inherited totality body',
  )
  const inheritedTransportAddition = exactOne(
    directNodes(backward.diagram, copiedTransportTotalityBody),
    'copied successor-transport inherited addition',
  )
  const inheritedTransportOutput = endpointWire(
    backward.diagram,
    inheritedTransportAddition,
    'arg',
    2,
  )
  backward.record('expose inherited transport addition witness', {
    rule: 'doubleCutElim',
    region: copiedTransportTotality,
  })

  before = backward.diagram
  backward.record('copy successor totality into successor transport', {
    rule: 'iteration',
    sel: {
      region: hypotheses,
      regions: [successorTotal],
      nodes: [],
      wires: [],
    },
    target: successorTransportAntecedent,
  })
  const copiedTransportSuccessorTotal = onlyNewCut(
    before,
    backward.diagram,
    successorTransportAntecedent,
  )
  const copiedTransportSuccessorBody = exactOne(
    directCuts(backward.diagram, copiedTransportSuccessorTotal),
    'copied successor-transport successor-totality body',
  )
  const inheritedOutputSuccessorNode = exactOne(
    directNodes(backward.diagram, copiedTransportSuccessorBody),
    'copied successor-transport output successor',
  )
  backward.record('specialize inherited output successor input', {
    rule: 'wireJoin',
    input: {
      a: inheritedTransportOutput,
      b: endpointWire(
        backward.diagram,
        inheritedOutputSuccessorNode,
        'arg',
        0,
      ),
    },
  })
  const inheritedOutputSuccessor = endpointWire(
    backward.diagram,
    inheritedOutputSuccessorNode,
    'arg',
    1,
  )
  backward.record('expose inherited output successor', {
    rule: 'doubleCutElim',
    region: copiedTransportSuccessorTotal,
  })

  const deriveClosureStep = (
    right: WireId,
    output: WireId,
    outputSuccessor: WireId,
    target: RegionId,
    label: string,
  ): NodeId => {
    const prior = backward.diagram
    backward.record(`copy addition step for ${label}`, {
      rule: 'iteration',
      sel: {
        region: hypotheses,
        regions: [additionStep],
        nodes: [],
        wires: [],
      },
      target,
      })
    const scope = onlyNewCut(prior, backward.diagram, target)
    const body = exactOne(
      directCuts(backward.diagram, scope),
      `${label} addition-step body`,
    )
    const antecedent = exactOne(
      directCuts(backward.diagram, body),
      `${label} addition-step antecedent`,
    )
    const consequent = exactOne(
      directCuts(backward.diagram, antecedent),
      `${label} addition-step consequent`,
    )
    const premises = directNodes(backward.diagram, antecedent)
    const plusPremise = exactOne(
      premises.filter((node) =>
        endpointWire(backward.diagram, node, 'head') === plus),
      `${label} addition-step Plus`,
    )
    const successorPremises = premises.filter((node) =>
      endpointWire(backward.diagram, node, 'head') === successor)
    if (successorPremises.length !== 2) {
      throw new Error(
        `expected two ${label} step successors, found ${successorPremises.length}`,
      )
    }
    const left = endpointWire(backward.diagram, plusPremise, 'arg', 0)
    const stepOutput = endpointWire(
      backward.diagram,
      plusPremise,
      'arg',
      2,
    )
    const leftSuccessor = exactOne(
      successorPremises.filter((node) =>
        endpointWire(backward.diagram, node, 'arg', 0) === left),
      `${label} left successor`,
    )
    const outputSuccessorPremise = exactOne(
      successorPremises.filter((node) =>
        endpointWire(backward.diagram, node, 'arg', 0) === stepOutput),
      `${label} output successor`,
    )
    for (const [binding, outer, inner] of [
      ['left', predecessor, left],
      [
        'right',
        right,
        endpointWire(backward.diagram, plusPremise, 'arg', 1),
      ],
      ['output', output, stepOutput],
      [
        'left successor',
        successorValue,
        endpointWire(backward.diagram, leftSuccessor, 'arg', 1),
      ],
      [
        'output successor',
        outputSuccessor,
        endpointWire(
          backward.diagram,
          outputSuccessorPremise,
          'arg',
          1,
        ),
      ],
    ] as const) {
      backward.record(`specialize ${label} ${binding}`, {
        rule: 'wireJoin',
        input: { a: outer, b: inner },
      })
    }
    for (const node of [
      plusPremise,
      leftSuccessor,
      outputSuccessorPremise,
    ]) {
      deiterateNode(
        backward,
        `discharge ${label} premise`,
        antecedent,
        node,
      )
    }
    const result = exactOne(
      directNodes(backward.diagram, consequent),
      `${label} result`,
    )
    backward.record(`expose ${label} result`, {
      rule: 'doubleCutElim',
      region: antecedent,
    })
    backward.record(`finish ${label} specialization`, {
      rule: 'doubleCutElim',
      region: scope,
    })
    return result
  }

  const canonicalSuccessorAddition = deriveClosureStep(
    closureRight,
    inheritedTransportOutput,
    inheritedOutputSuccessor,
    successorTransportAntecedent,
    'successor-transport canonical addition',
  )

  before = backward.diagram
  backward.record('copy addition functionality into successor transport', {
    rule: 'iteration',
    sel: {
      region: hypotheses,
      regions: [additionFunctional],
      nodes: [],
      wires: [],
    },
    target: successorTransportAntecedent,
  })
  const copiedTransportFunctionality = onlyNewCut(
    before,
    backward.diagram,
    successorTransportAntecedent,
  )
  const copiedTransportFunctionalityBody = exactOne(
    directCuts(backward.diagram, copiedTransportFunctionality),
    'successor-transport functionality body',
  )
  const copiedTransportFunctionalityAntecedent = exactOne(
    directCuts(backward.diagram, copiedTransportFunctionalityBody),
    'successor-transport functionality antecedent',
  )
  const copiedTransportFunctionalityConsequent = exactOne(
    directCuts(backward.diagram, copiedTransportFunctionalityAntecedent),
    'successor-transport functionality consequent',
  )
  const transportFunctionalPluses = directNodes(
    backward.diagram,
    copiedTransportFunctionalityAntecedent,
  )
  if (transportFunctionalPluses.length !== 2) {
    throw new Error(
      `expected two successor-transport functional Plus premises, found ${transportFunctionalPluses.length}`,
    )
  }
  const [transportFunctionalFirst, transportFunctionalSecond] =
    transportFunctionalPluses
  for (const [label, outer, inner] of [
    [
      'left',
      successorValue,
      endpointWire(backward.diagram, transportFunctionalFirst!, 'arg', 0),
    ],
    [
      'right',
      closureRight,
      endpointWire(backward.diagram, transportFunctionalFirst!, 'arg', 1),
    ],
    [
      'actual output',
      closureOutput,
      endpointWire(backward.diagram, transportFunctionalFirst!, 'arg', 2),
    ],
    [
      'canonical output',
      inheritedOutputSuccessor,
      endpointWire(backward.diagram, transportFunctionalSecond!, 'arg', 2),
    ],
  ] as const) {
    backward.record(`specialize successor-transport functionality ${label}`, {
      rule: 'wireJoin',
      input: { a: outer, b: inner },
    })
  }
  deiterateNode(
    backward,
    'discharge successor-transport actual addition',
    copiedTransportFunctionalityAntecedent,
    transportFunctionalFirst!,
  )
  deiterateNode(
    backward,
    'discharge successor-transport canonical addition',
    copiedTransportFunctionalityAntecedent,
    transportFunctionalSecond!,
  )
  exactOne(
    directNodes(backward.diagram, copiedTransportFunctionalityConsequent),
    'successor-transport output identity',
  )
  backward.record('expose successor-transport output identity', {
    rule: 'doubleCutElim',
    region: copiedTransportFunctionalityAntecedent,
  })
  // Finishing exposes id(actual output, canonical output) with one outer
  // wire; the one-point collapse merges them on the spot, so the output
  // successor copies as a plain iteration onto the merged wire.
  backward.record('finish successor-transport functionality', {
    rule: 'doubleCutElim',
    region: copiedTransportFunctionality,
  })

  before = backward.diagram
  backward.record('transport output successor to inherited output', {
    rule: 'iteration',
    sel: {
      region: successorTransportAntecedent,
      regions: [],
      nodes: [closureOutputSuccessorNode],
      wires: [],
    },
    target: successorTransportAntecedent,
  })
  const transportedOutputSuccessor = onlyNewNode(
    before,
    backward.diagram,
    successorTransportAntecedent,
  )

  before = backward.diagram
  backward.record('copy inherited shift into successor transport', {
    rule: 'iteration',
    sel: {
      region: closureAntecedent,
      regions: [predecessorTransport],
      nodes: [],
      wires: [],
    },
    target: successorTransportAntecedent,
  })
  const copiedInheritedShift = onlyNewCut(
    before,
    backward.diagram,
    successorTransportAntecedent,
  )
  const copiedInheritedShiftBody = exactOne(
    directCuts(backward.diagram, copiedInheritedShift),
    'copied inherited shift body',
  )
  const copiedInheritedShiftAntecedent = exactOne(
    directCuts(backward.diagram, copiedInheritedShiftBody),
    'copied inherited shift antecedent',
  )
  const copiedInheritedShiftConsequent = exactOne(
    directCuts(backward.diagram, copiedInheritedShiftAntecedent),
    'copied inherited shift consequent',
  )
  const copiedInheritedShiftPremises = directNodes(
    backward.diagram,
    copiedInheritedShiftAntecedent,
  )
  const copiedInheritedShiftPlus = exactOne(
    copiedInheritedShiftPremises.filter((node) =>
      endpointWire(backward.diagram, node, 'head') === plus),
    'copied inherited shift Plus',
  )
  const copiedInheritedShiftSuccessors =
    copiedInheritedShiftPremises.filter((node) =>
      endpointWire(backward.diagram, node, 'head') === successor)
  if (copiedInheritedShiftSuccessors.length !== 2) {
    throw new Error(
      `expected two inherited shift successors, found ${copiedInheritedShiftSuccessors.length}`,
    )
  }
  const inheritedShiftRight = endpointWire(
    backward.diagram,
    copiedInheritedShiftPlus,
    'arg',
    1,
  )
  const inheritedShiftOutput = endpointWire(
    backward.diagram,
    copiedInheritedShiftPlus,
    'arg',
    2,
  )
  const inheritedShiftRightSuccessor = exactOne(
    copiedInheritedShiftSuccessors.filter((node) =>
      endpointWire(backward.diagram, node, 'arg', 0)
        === inheritedShiftRight),
    'copied inherited right successor',
  )
  const inheritedShiftOutputSuccessor = exactOne(
    copiedInheritedShiftSuccessors.filter((node) =>
      endpointWire(backward.diagram, node, 'arg', 0)
        === inheritedShiftOutput),
    'copied inherited output successor',
  )
  for (const [label, outer, inner] of [
    ['right', closureRight, inheritedShiftRight],
    [
      'right successor',
      closureRightSuccessor,
      endpointWire(
        backward.diagram,
        inheritedShiftRightSuccessor,
        'arg',
        1,
      ),
    ],
    ['output', inheritedTransportOutput, inheritedShiftOutput],
    [
      'output successor',
      inheritedOutputSuccessor,
      endpointWire(
        backward.diagram,
        inheritedShiftOutputSuccessor,
        'arg',
        1,
      ),
    ],
  ] as const) {
    backward.record(`specialize inherited shift ${label}`, {
      rule: 'wireJoin',
      input: { a: outer, b: inner },
    })
  }
  for (const node of [
    copiedInheritedShiftPlus,
    inheritedShiftRightSuccessor,
    inheritedShiftOutputSuccessor,
  ]) {
    deiterateNode(
      backward,
      'discharge inherited shift premise',
      copiedInheritedShiftAntecedent,
      node,
    )
  }
  const inheritedShiftResult = exactOne(
    directNodes(backward.diagram, copiedInheritedShiftConsequent),
    'copied inherited shift result',
  )
  backward.record('expose inherited shift result', {
    rule: 'doubleCutElim',
    region: copiedInheritedShiftAntecedent,
  })
  backward.record('finish inherited shift specialization', {
    rule: 'doubleCutElim',
    region: copiedInheritedShift,
  })

  const finalShiftResult = deriveClosureStep(
    closureRightSuccessor,
    inheritedOutputSuccessor,
    closureOutputSuccessor,
    successorTransportAntecedent,
    'successor-transport final shift',
  )
  deiterateNode(
    backward,
    'discharge closure successor-shift goal',
    successorTransportConsequent,
    successorTransportGoal,
  )

  void canonicalSuccessorAddition
  void transportedOutputSuccessor
  void inheritedShiftResult
  void finalShiftResult

  return {
    name: 'successorShiftCarrierInductive',
    lhs,
    rhs,
    actions: forward.actions,
    backActions: backward.actions,
  }
}
