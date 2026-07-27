import type { WireId } from '../kernel/diagram/diagram'
import { extractSubgraph } from '../kernel/diagram/subgraph/extract'
import { findDeiterationEvidence } from '../kernel/rules/iteration'
import { IOTA, relSig } from '../kernel/diagram/sig'
import type { ProofContext } from '../kernel/proof/context'
import type { Theorem } from '../kernel/proof/theorem'
import {
  BINARY,
  TERNARY,
  UNARY,
  associativityCarrierContent,
  deiterationStep,
  directCuts,
  directNodes,
  endpointWire,
  exactOne,
  relationWire,
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

function exactHypothesesContent() {
  let graph = emptyGraph()
  const successor = declareWire(graph, graph.root, BINARY)
  graph = successor.graph
  const plus = declareWire(graph, graph.root, TERNARY)
  graph = plus.graph

  const totalVariables = quantifierScope(
    graph,
    graph.root,
    'forall',
    [IOTA],
  )
  graph = totalVariables.graph
  const totalOutput = declareWire(
    graph,
    totalVariables.value.body,
    IOTA,
  )
  graph = totalOutput.graph
  graph = atom(
    graph,
    totalVariables.value.body,
    successor.value,
    [totalVariables.value.variables[0]!, totalOutput.value],
  ).graph

  const stepVariables = quantifierScope(
    graph,
    graph.root,
    'forall',
    [IOTA, IOTA, IOTA, IOTA, IOTA],
  )
  graph = stepVariables.graph
  const [
    left,
    right,
    output,
    leftSuccessor,
    outputSuccessor,
  ] = stepVariables.value.variables
  const stepClaim = implication(graph, stepVariables.value.body)
  graph = stepClaim.graph
  graph = atom(
    graph,
    stepClaim.value.antecedent,
    plus.value,
    [left!, right!, output!],
  ).graph
  graph = atom(
    graph,
    stepClaim.value.antecedent,
    successor.value,
    [left!, leftSuccessor!],
  ).graph
  graph = atom(
    graph,
    stepClaim.value.antecedent,
    successor.value,
    [output!, outputSuccessor!],
  ).graph
  graph = atom(
    graph,
    stepClaim.value.consequent,
    plus.value,
    [leftSuccessor!, right!, outputSuccessor!],
  ).graph

  const functionalVariables = quantifierScope(
    graph,
    graph.root,
    'forall',
    [IOTA, IOTA, IOTA, IOTA],
  )
  graph = functionalVariables.graph
  const [functionalLeft, functionalRight, first, second] =
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
    [functionalLeft!, functionalRight!, first!],
  ).graph
  graph = atom(
    graph,
    functionalClaim.value.antecedent,
    plus.value,
    [functionalLeft!, functionalRight!, second!],
  ).graph
  graph = identity(
    graph,
    functionalClaim.value.consequent,
    [first!, second!],
  ).graph

  return finishDiagramWithBoundary(graph, [successor.value, plus.value])
}
export function associativityCarrierHereditary(
  statements: ArithmeticStatements,
  context: ProofContext,
): Theorem {
  const lhs = finishDiagramWithBoundary(emptyGraph(), [])
  const forward = new PrimitiveStepRecorder(lhs.diagram, context)

  let before = forward.diagram
  forward.record('open primitive universal scope', {
    rule: 'doubleCutIntro',
    sel: {
      region: forward.diagram.root,
      regions: [],
      nodes: [],
      wires: [],
    },
  })
  const primitiveScope = onlyNewCut(
    before,
    forward.diagram,
    forward.diagram.root,
  )
  const primitiveBody = exactOne(
    directCuts(forward.diagram, primitiveScope),
    'helper primitive universal body',
  )

  before = forward.diagram
  forward.record('introduce helper-local successor relation', {
    rule: 'vacuousIntro',
    scope: primitiveScope,
    sig: BINARY,
  })
  const successor = onlyNewWire(
    before,
    forward.diagram,
    primitiveScope,
  )

  before = forward.diagram
  forward.record('introduce helper-local addition relation', {
    rule: 'vacuousIntro',
    scope: primitiveScope,
    sig: TERNARY,
  })
  const plus = onlyNewWire(before, forward.diagram, primitiveScope)

  before = forward.diagram
  forward.record('open helper standing-hypothesis implication', {
    rule: 'doubleCutIntro',
    sel: {
      region: primitiveBody,
      regions: [],
      nodes: [],
      wires: [],
    },
  })
  const hypotheses = onlyNewCut(before, forward.diagram, primitiveBody)
  const conclusion = exactOne(
    directCuts(forward.diagram, hypotheses),
    'helper conclusion',
  )

  before = forward.diagram
  forward.record('introduce temporary standing hypotheses', {
    rule: 'vacuousIntro',
    scope: hypotheses,
    sig: relSig([]),
  })
  const temporaryHypotheses = onlyNewWire(
    before,
    forward.diagram,
    hypotheses,
  )
  before = forward.diagram
  forward.record('assert temporary standing hypotheses', {
    rule: 'atomSpawn',
    region: hypotheses,
    wire: temporaryHypotheses,
  })
  onlyNewNode(before, forward.diagram, hypotheses)
  forward.record('ground exact standing hypotheses', {
    rule: 'wireJoin',
    input: {
      kind: 'relation',
      wire: temporaryHypotheses,
      content: exactHypothesesContent(),
      parameters: [successor, plus],
    },
  })

  before = forward.diagram
  forward.record('open hereditary universal scope', {
    rule: 'doubleCutIntro',
    sel: {
      region: conclusion,
      regions: [],
      nodes: [],
      wires: [],
    },
  })
  const hereditaryScope = onlyNewCut(
    before,
    forward.diagram,
    conclusion,
  )
  const hereditaryBody = exactOne(
    directCuts(forward.diagram, hereditaryScope),
    'hereditary body',
  )
  const hereditaryVariables: WireId[] = []
  for (const label of ['predecessor', 'successor']) {
    before = forward.diagram
    forward.record(`introduce hereditary ${label}`, {
      rule: 'vacuousIntro',
      scope: hereditaryScope,
      sig: IOTA,
    })
    hereditaryVariables.push(
      onlyNewWire(before, forward.diagram, hereditaryScope),
    )
  }
  const [predecessor, successorValue] = hereditaryVariables

  before = forward.diagram
  forward.record('open hereditary implication', {
    rule: 'doubleCutIntro',
    sel: {
      region: hereditaryBody,
      regions: [],
      nodes: [],
      wires: [],
    },
  })
  const hereditaryAntecedent = onlyNewCut(
    before,
    forward.diagram,
    hereditaryBody,
  )
  const hereditaryConsequent = exactOne(
    directCuts(forward.diagram, hereditaryAntecedent),
    'hereditary consequent',
  )

  before = forward.diagram
  forward.record('introduce temporary predecessor carrier', {
    rule: 'vacuousIntro',
    scope: hereditaryAntecedent,
    sig: UNARY,
  })
  const temporaryCarrier = onlyNewWire(
    before,
    forward.diagram,
    hereditaryAntecedent,
  )
  before = forward.diagram
  forward.record('assert temporary predecessor carrier', {
    rule: 'atomSpawn',
    region: hereditaryAntecedent,
    wire: temporaryCarrier,
  })
  const temporaryCarrierNode = onlyNewNode(
    before,
    forward.diagram,
    hereditaryAntecedent,
  )
  forward.record('attach predecessor carrier individual', {
    rule: 'wireJoin',
    input: {
      kind: 'iota',
      a: predecessor!,
      b: endpointWire(
        forward.diagram,
        temporaryCarrierNode,
        'arg',
        0,
      ),
    },
  })
  forward.record('ground exact predecessor carrier', {
    rule: 'wireJoin',
    input: {
      kind: 'relation',
      wire: temporaryCarrier,
      content: associativityCarrierContent(),
      parameters: [plus],
    },
  })

  const spawnAtom = (
    region: string,
    head: string,
    args: readonly string[],
    label: string,
  ) => {
    const prior = forward.diagram
    forward.record(`insert ${label}`, {
      rule: 'atomSpawn',
      region,
      wire: head,
    })
    const node = onlyNewNode(prior, forward.diagram, region)
    for (let index = 0; index < args.length; index += 1) {
      forward.record(`attach ${label} argument ${index}`, {
        rule: 'wireJoin',
        input: {
          kind: 'iota',
          a: args[index]!,
          b: endpointWire(forward.diagram, node, 'arg', index),
        },
      })
    }
    return node
  }

  spawnAtom(
    hereditaryAntecedent,
    successor,
    [predecessor!, successorValue!],
    'hereditary successor premise',
  )

  before = forward.diagram
  forward.record('open successor totality scope', {
    rule: 'doubleCutIntro',
    sel: {
      region: hereditaryConsequent,
      regions: [],
      nodes: [],
      wires: [],
    },
  })
  const successorTotalityScope = onlyNewCut(
    before,
    forward.diagram,
    hereditaryConsequent,
  )
  for (const label of ['right', 'predecessor sum', 'successor sum']) {
    before = forward.diagram
    forward.record(`introduce successor-totality ${label}`, {
      rule: 'vacuousIntro',
      scope: successorTotalityScope,
      sig: IOTA,
    })
  }
  const successorTotalityWires = scopedWires(
    forward.diagram,
    successorTotalityScope,
  )
  const [totalityRight, forwardPredecessorSum, forwardSuccessorSum] =
    successorTotalityWires
  spawnAtom(
    successorTotalityScope,
    plus,
    [predecessor!, totalityRight!, forwardPredecessorSum!],
    'predecessor totality evidence',
  )
  spawnAtom(
    successorTotalityScope,
    successor,
    [forwardPredecessorSum!, forwardSuccessorSum!],
    'successor-sum evidence',
  )
  spawnAtom(
    successorTotalityScope,
    plus,
    [successorValue!, totalityRight!, forwardSuccessorSum!],
    'successor totality evidence',
  )

  before = forward.diagram
  forward.record('open successor transport scope', {
    rule: 'doubleCutIntro',
    sel: {
      region: hereditaryConsequent,
      regions: [],
      nodes: [],
      wires: [],
    },
  })
  const successorTransportScope = onlyNewCut(
    before,
    forward.diagram,
    hereditaryConsequent,
  )
  for (const label of ['right', 'third', 'first sum', 'inner sum']) {
    before = forward.diagram
    forward.record(`introduce successor-transport ${label}`, {
      rule: 'vacuousIntro',
      scope: successorTransportScope,
      sig: IOTA,
    })
  }
  const [
    forwardTransportRight,
    forwardTransportThird,
    forwardTransportFirstSum,
    forwardTransportInnerSum,
  ] = scopedWires(forward.diagram, successorTransportScope)
  const forwardSuccessorTransportBody = exactOne(
    directCuts(forward.diagram, successorTransportScope),
    'successor transport body',
  )
  before = forward.diagram
  forward.record('open successor transport implication', {
    rule: 'doubleCutIntro',
    sel: {
      region: forwardSuccessorTransportBody,
      regions: [],
      nodes: [],
      wires: [],
    },
  })
  const forwardSuccessorTransportAntecedent = onlyNewCut(
    before,
    forward.diagram,
    forwardSuccessorTransportBody,
  )
  for (const label of [
    'predecessor sum',
    'successor sum',
    'predecessor output',
    'successor output',
  ]) {
    before = forward.diagram
    forward.record(`introduce transport evidence ${label}`, {
      rule: 'vacuousIntro',
      scope: forwardSuccessorTransportAntecedent,
      sig: IOTA,
    })
  }
  const [
    forwardTransportPredecessorSum,
    forwardTransportSuccessorSum,
    forwardTransportPredecessorOutput,
    forwardTransportSuccessorOutput,
  ] = scopedWires(forward.diagram, forwardSuccessorTransportAntecedent)

  spawnAtom(
    forwardSuccessorTransportAntecedent,
    plus,
    [forwardTransportRight!, forwardTransportThird!, forwardTransportInnerSum!],
    'successor inner premise',
  )
  spawnAtom(
    forwardSuccessorTransportAntecedent,
    plus,
    [predecessor!, forwardTransportRight!, forwardTransportPredecessorSum!],
    'transport predecessor totality',
  )
  spawnAtom(
    forwardSuccessorTransportAntecedent,
    successor,
    [forwardTransportPredecessorSum!, forwardTransportSuccessorSum!],
    'transport predecessor-sum successor',
  )
  spawnAtom(
    forwardSuccessorTransportAntecedent,
    plus,
    [successorValue!, forwardTransportRight!, forwardTransportSuccessorSum!],
    'transport specialized first result',
  )
  before = forward.diagram
  forward.record('insert transport first-sum identity', {
    rule: 'identityInsert',
    region: forwardSuccessorTransportAntecedent,
    wires: [forwardTransportSuccessorSum!, forwardTransportFirstSum!],
  })
  spawnAtom(
    forwardSuccessorTransportAntecedent,
    plus,
    [predecessor!, forwardTransportInnerSum!, forwardTransportPredecessorOutput!],
    'predecessor outer transport result',
  )
  spawnAtom(
    forwardSuccessorTransportAntecedent,
    plus,
    [forwardTransportPredecessorSum!, forwardTransportThird!, forwardTransportPredecessorOutput!],
    'predecessor first transport result',
  )
  spawnAtom(
    forwardSuccessorTransportAntecedent,
    successor,
    [forwardTransportPredecessorOutput!, forwardTransportSuccessorOutput!],
    'transport output successor',
  )
  spawnAtom(
    forwardSuccessorTransportAntecedent,
    plus,
    [forwardTransportSuccessorSum!, forwardTransportThird!, forwardTransportSuccessorOutput!],
    'stepped first transport result',
  )
  spawnAtom(
    forwardSuccessorTransportAntecedent,
    plus,
    [successorValue!, forwardTransportInnerSum!, forwardTransportSuccessorOutput!],
    'stepped outer transport result',
  )
  spawnAtom(
    forwardSuccessorTransportAntecedent,
    plus,
    [forwardTransportFirstSum!, forwardTransportThird!, forwardTransportSuccessorOutput!],
    'retargeted first transport result',
  )

  const rhs = statements.associativityCarrierHereditary
  const backward = new PrimitiveStepRecorder(
    rhs.diagram,
    context,
    'backward',
  )
  const reviewedPrimitiveScope = exactOne(
    directCuts(backward.diagram, backward.diagram.root),
    'reviewed helper primitive scope',
  )
  const reviewedPrimitiveBody = exactOne(
    directCuts(backward.diagram, reviewedPrimitiveScope),
    'reviewed helper primitive body',
  )
  const reviewedHypotheses = exactOne(
    directCuts(backward.diagram, reviewedPrimitiveBody),
    'reviewed helper standing-hypothesis antecedent',
  )
  const reviewedChildren = directCuts(
    backward.diagram,
    reviewedHypotheses,
  )
  const reviewedConclusion = exactOne(
    reviewedChildren.filter((region) =>
      scopedWires(backward.diagram, region).length === 0),
    'reviewed helper conclusion',
  )
  const reviewedSuccessorTotal = exactOne(
    reviewedChildren.filter((region) =>
      scopedWires(backward.diagram, region).length === 1),
    'reviewed successorTotal hypothesis',
  )
  const reviewedAdditionStep = exactOne(
    reviewedChildren.filter((region) =>
      scopedWires(backward.diagram, region).length === 5),
    'reviewed plusStep hypothesis',
  )
  const reviewedAdditionFunctional = exactOne(
    reviewedChildren.filter((region) =>
      scopedWires(backward.diagram, region).length === 4),
    'reviewed plusSingleValued hypothesis',
  )
  const reviewedPlus = relationWire(
    backward.diagram,
    reviewedPrimitiveScope,
    TERNARY,
  )
  const reviewedSuccessor = relationWire(
    backward.diagram,
    reviewedPrimitiveScope,
    BINARY,
  )
  const helperClosure = exactOne(
    directCuts(backward.diagram, reviewedConclusion),
    'reviewed helper carrier closure',
  )
  const helperClosureBody = exactOne(
    directCuts(backward.diagram, helperClosure),
    'reviewed helper carrier closure body',
  )
  const helperClosureAntecedent = exactOne(
    directCuts(backward.diagram, helperClosureBody),
    'reviewed helper carrier closure antecedent',
  )
  const helperClosureConsequent = exactOne(
    directCuts(backward.diagram, helperClosureAntecedent)
      .filter((region) =>
        scopedWires(backward.diagram, region).length === 0),
    'reviewed helper carrier closure consequent',
  )
  const helperClosureVariables = scopedWires(
    backward.diagram,
    helperClosure,
  )
  if (helperClosureVariables.length !== 2) {
    throw new Error('expected predecessor and successor closure variables')
  }
  const [helperClosurePredecessor, helperClosureSuccessor] =
    helperClosureVariables
  const predecessorAssertions = directCuts(
    backward.diagram,
    helperClosureAntecedent,
  ).filter((region) => region !== helperClosureConsequent)
  const predecessorTotality = exactOne(
    predecessorAssertions.filter((region) =>
      scopedWires(backward.diagram, region).length === 1),
    'exposed closure-predecessor totality',
  )
  const predecessorTransport = exactOne(
    predecessorAssertions.filter((region) =>
      scopedWires(backward.diagram, region).length === 4),
    'exposed closure-predecessor transport',
  )

  const successorAssertions = directCuts(
    backward.diagram,
    helperClosureConsequent,
  )
  const successorTotality = exactOne(
    successorAssertions.filter((region) =>
      scopedWires(backward.diagram, region).length === 1),
    'closure-successor totality',
  )
  const successorTransport = exactOne(
    successorAssertions.filter((region) =>
      scopedWires(backward.diagram, region).length === 4),
    'closure-successor transport',
  )
  const closureSuccessorPremise = exactOne(
    directNodes(backward.diagram, helperClosureAntecedent).filter((node) =>
      backward.diagram.nodes[node]!.kind === 'atom'
      && endpointWire(backward.diagram, node, 'head')
        === reviewedSuccessor),
    'closure successor premise',
  )
  const successorTotalityInput = exactOne(
    scopedWires(backward.diagram, successorTotality),
    'successor totality input',
  )
  const successorTotalityBody = exactOne(
    directCuts(backward.diagram, successorTotality),
    'successor totality body',
  )
  const successorTotalityGoal = exactOne(
    directNodes(backward.diagram, successorTotalityBody).filter((node) =>
      backward.diagram.nodes[node]!.kind === 'atom'
      && endpointWire(backward.diagram, node, 'head') === reviewedPlus),
    'successor totality goal',
  )
  const successorTotalityOutput = endpointWire(
    backward.diagram,
    successorTotalityGoal,
    'arg',
    2,
  )

  before = backward.diagram
  backward.record('copy predecessor totality into successor totality', {
    rule: 'iteration',
    sel: {
      region: helperClosureAntecedent,
      regions: [predecessorTotality],
      nodes: [],
      wires: [],
    },
    target: successorTotality,
    retargets: [],
  })
  const copiedPredecessorTotality = onlyNewCut(
    before,
    backward.diagram,
    successorTotality,
  )
  const copiedPredecessorTotalityInput = exactOne(
    scopedWires(backward.diagram, copiedPredecessorTotality),
    'copied predecessor totality input',
  )
  backward.record('specialize predecessor totality at successor right input', {
    rule: 'wireJoin',
    input: {
      kind: 'iota',
      a: successorTotalityInput,
      b: copiedPredecessorTotalityInput,
    },
  })
  const copiedPredecessorTotalityBody = exactOne(
    directCuts(backward.diagram, copiedPredecessorTotality),
    'copied predecessor totality body',
  )
  const copiedPredecessorPlus = exactOne(
    directNodes(backward.diagram, copiedPredecessorTotalityBody).filter(
      (node) =>
        backward.diagram.nodes[node]!.kind === 'atom'
        && endpointWire(backward.diagram, node, 'head') === reviewedPlus,
    ),
    'copied predecessor totality result',
  )
  const predecessorSum = endpointWire(
    backward.diagram,
    copiedPredecessorPlus,
    'arg',
    2,
  )
  backward.record('expose predecessor totality result', {
    rule: 'doubleCutElim',
    region: copiedPredecessorTotality,
  })

  before = backward.diagram
  backward.record('copy successor totality for predecessor sum', {
    rule: 'iteration',
    sel: {
      region: reviewedHypotheses,
      regions: [reviewedSuccessorTotal!],
      nodes: [],
      wires: [],
    },
    target: successorTotality,
    retargets: [],
  })
  const copiedSuccessorTotality = onlyNewCut(
    before,
    backward.diagram,
    successorTotality,
  )
  const copiedSuccessorInput = exactOne(
    scopedWires(backward.diagram, copiedSuccessorTotality),
    'copied successor-totality input',
  )
  backward.record('specialize successor totality at predecessor sum', {
    rule: 'wireJoin',
    input: {
      kind: 'iota',
      a: predecessorSum,
      b: copiedSuccessorInput,
    },
  })
  const copiedSuccessorBody = exactOne(
    directCuts(backward.diagram, copiedSuccessorTotality),
    'copied successor-totality body',
  )
  const copiedOutputSuccessor = exactOne(
    directNodes(backward.diagram, copiedSuccessorBody).filter((node) =>
      backward.diagram.nodes[node]!.kind === 'atom'
      && endpointWire(backward.diagram, node, 'head')
        === reviewedSuccessor),
    'copied output successor',
  )
  const successorSum = endpointWire(
    backward.diagram,
    copiedOutputSuccessor,
    'arg',
    1,
  )
  backward.record('expose successor of predecessor sum', {
    rule: 'doubleCutElim',
    region: copiedSuccessorTotality,
  })
  backward.record('choose successor-totality output witness', {
    rule: 'wireJoin',
    input: {
      kind: 'iota',
      a: successorSum,
      b: successorTotalityOutput,
    },
  })

  before = backward.diagram
  backward.record('copy addition step into successor totality', {
    rule: 'iteration',
    sel: {
      region: reviewedHypotheses,
      regions: [reviewedAdditionStep!],
      nodes: [],
      wires: [],
    },
    target: successorTotality,
    retargets: [],
  })
  const copiedTotalityStep = onlyNewCut(
    before,
    backward.diagram,
    successorTotality,
  )
  const copiedTotalityStepVariables = scopedWires(
    backward.diagram,
    copiedTotalityStep,
  )
  if (copiedTotalityStepVariables.length !== 5) {
    throw new Error('expected five copied totality-step variables')
  }
  for (const [target, variable] of [
    [helperClosurePredecessor!, copiedTotalityStepVariables[0]!],
    [successorTotalityInput, copiedTotalityStepVariables[1]!],
    [predecessorSum, copiedTotalityStepVariables[2]!],
    [helperClosureSuccessor!, copiedTotalityStepVariables[3]!],
    [successorSum, copiedTotalityStepVariables[4]!],
  ] as const) {
    backward.record('specialize successor-totality addition step', {
      rule: 'wireJoin',
      input: {
        kind: 'iota',
        a: target,
        b: variable,
      },
    })
  }
  const copiedTotalityStepBody = exactOne(
    directCuts(backward.diagram, copiedTotalityStep),
    'copied totality-step body',
  )
  const copiedTotalityStepAntecedent = exactOne(
    directCuts(backward.diagram, copiedTotalityStepBody),
    'copied totality-step antecedent',
  )
  const copiedTotalityStepConsequent = exactOne(
    directCuts(backward.diagram, copiedTotalityStepAntecedent),
    'copied totality-step consequent',
  )
  for (const premise of directNodes(
    backward.diagram,
    copiedTotalityStepAntecedent,
  )) {
    backward.record(
      'discharge successor-totality addition-step premise',
      deiterationStep(
        backward.diagram,
        copiedTotalityStepAntecedent,
        premise,
      ),
    )
  }
  const copiedTotalityResult = exactOne(
    directNodes(backward.diagram, copiedTotalityStepConsequent).filter(
      (node) =>
        backward.diagram.nodes[node]!.kind === 'atom'
        && endpointWire(backward.diagram, node, 'head') === reviewedPlus,
    ),
    'copied successor-totality result',
  )
  backward.record('expose successor-totality addition result', {
    rule: 'doubleCutElim',
    region: copiedTotalityStepAntecedent,
  })
  backward.record('finish successor-totality addition step', {
    rule: 'doubleCutElim',
    region: copiedTotalityStep,
  })
  backward.record(
    'discharge successor totality goal',
    deiterationStep(
      backward.diagram,
      successorTotalityBody,
      successorTotalityGoal,
    ),
  )

  const successorTransportVariables = scopedWires(
    backward.diagram,
    successorTransport,
  )
  if (successorTransportVariables.length !== 4) {
    throw new Error('expected four successor-transport variables')
  }
  const [
    transportRight,
    transportThird,
    transportFirstSum,
    transportInnerSum,
  ] = successorTransportVariables
  const successorTransportBody = exactOne(
    directCuts(backward.diagram, successorTransport),
    'successor transport body',
  )
  const successorTransportAntecedent = exactOne(
    directCuts(backward.diagram, successorTransportBody),
    'successor transport antecedent',
  )
  const successorTransportConsequent = exactOne(
    directCuts(backward.diagram, successorTransportAntecedent),
    'successor transport consequent',
  )
  const successorTransportPremises = directNodes(
    backward.diagram,
    successorTransportAntecedent,
  ).filter((node) =>
    backward.diagram.nodes[node]!.kind === 'atom'
    && endpointWire(backward.diagram, node, 'head') === reviewedPlus)
  const successorFirstPremise = exactOne(
    successorTransportPremises.filter((node) =>
      endpointWire(backward.diagram, node, 'arg', 0)
        === helperClosureSuccessor),
    'successor transport first premise',
  )
  const successorInnerPremise = exactOne(
    successorTransportPremises.filter((node) =>
      node !== successorFirstPremise),
    'successor transport inner premise',
  )
  const successorTransportGoals = directNodes(
    backward.diagram,
    successorTransportConsequent,
  ).filter((node) =>
    backward.diagram.nodes[node]!.kind === 'atom'
    && endpointWire(backward.diagram, node, 'head') === reviewedPlus)
  const successorOuterGoal = exactOne(
    successorTransportGoals.filter((node) =>
      endpointWire(backward.diagram, node, 'arg', 0)
        === helperClosureSuccessor),
    'successor transport outer goal',
  )
  const successorFirstGoal = exactOne(
    successorTransportGoals.filter((node) =>
      node !== successorOuterGoal),
    'successor transport first-sum goal',
  )
  const successorTransportOutput = endpointWire(
    backward.diagram,
    successorOuterGoal,
    'arg',
    2,
  )

  const copySpecializedScope = (
    sourceParent: string,
    sourceScope: string,
    target: string,
    values: readonly string[],
    label: string,
  ) => {
    const prior = backward.diagram
    backward.record(`copy ${label}`, {
      rule: 'iteration',
      sel: {
        region: sourceParent,
        regions: [sourceScope],
        nodes: [],
        wires: [],
      },
      target,
      retargets: [],
    })
    const scope = onlyNewCut(prior, backward.diagram, target)
    const variables = scopedWires(backward.diagram, scope)
    if (variables.length !== values.length) {
      throw new Error(
        `expected ${values.length} ${label} variables, found ${variables.length}`,
      )
    }
    for (let index = 0; index < values.length; index += 1) {
      backward.record(`specialize ${label} variable ${index}`, {
        rule: 'wireJoin',
        input: {
          kind: 'iota',
          a: values[index]!,
          b: variables[index]!,
        },
      })
    }
    return {
      scope,
      body: exactOne(
        directCuts(backward.diagram, scope),
        `${label} body`,
      ),
    }
  }

  const transportPredecessorTotality = copySpecializedScope(
    helperClosureAntecedent,
    predecessorTotality,
    successorTransportAntecedent,
    [transportRight!],
    'predecessor totality for transport',
  )
  const transportPredecessorPlus = exactOne(
    directNodes(
      backward.diagram,
      transportPredecessorTotality.body,
    ).filter((node) =>
      backward.diagram.nodes[node]!.kind === 'atom'
      && endpointWire(backward.diagram, node, 'head') === reviewedPlus),
    'transport predecessor-totality result',
  )
  const transportPredecessorSum = endpointWire(
    backward.diagram,
    transportPredecessorPlus,
    'arg',
    2,
  )
  backward.record('expose transport predecessor-totality result', {
    rule: 'doubleCutElim',
    region: transportPredecessorTotality.scope,
  })

  const transportSumSuccessor = copySpecializedScope(
    reviewedHypotheses,
    reviewedSuccessorTotal!,
    successorTransportAntecedent,
    [transportPredecessorSum],
    'successor totality for transport predecessor sum',
  )
  const transportSumSuccessorNode = exactOne(
    directNodes(backward.diagram, transportSumSuccessor.body).filter(
      (node) =>
        backward.diagram.nodes[node]!.kind === 'atom'
        && endpointWire(backward.diagram, node, 'head')
          === reviewedSuccessor,
    ),
    'transport predecessor-sum successor',
  )
  const transportSuccessorSum = endpointWire(
    backward.diagram,
    transportSumSuccessorNode,
    'arg',
    1,
  )
  backward.record('expose transport predecessor-sum successor', {
    rule: 'doubleCutElim',
    region: transportSumSuccessor.scope,
  })

  const deriveSteppedAddition = (
    left: string,
    right: string,
    output: string,
    leftSuccessor: string,
    outputSuccessor: string,
    label: string,
  ) => {
    const copied = copySpecializedScope(
      reviewedHypotheses,
      reviewedAdditionStep!,
      successorTransportAntecedent,
      [left, right, output, leftSuccessor, outputSuccessor],
      label,
    )
    const antecedent = exactOne(
      directCuts(backward.diagram, copied.body),
      `${label} antecedent`,
    )
    const consequent = exactOne(
      directCuts(backward.diagram, antecedent),
      `${label} consequent`,
    )
    for (const premise of directNodes(backward.diagram, antecedent)) {
      backward.record(
        `discharge ${label} premise`,
        deiterationStep(backward.diagram, antecedent, premise),
      )
    }
    const result = exactOne(
      directNodes(backward.diagram, consequent).filter((node) =>
        backward.diagram.nodes[node]!.kind === 'atom'
        && endpointWire(backward.diagram, node, 'head') === reviewedPlus),
      `${label} result`,
    )
    backward.record(`expose ${label} result`, {
      rule: 'doubleCutElim',
      region: antecedent,
    })
    backward.record(`finish ${label}`, {
      rule: 'doubleCutElim',
      region: copied.scope,
    })
    return result
  }

  const transportSpecializedFirst = deriveSteppedAddition(
    helperClosurePredecessor!,
    transportRight!,
    transportPredecessorSum,
    helperClosureSuccessor!,
    transportSuccessorSum,
    'transport first addition step',
  )

  before = backward.diagram
  backward.record('copy transport first-sum functionality', {
    rule: 'iteration',
    sel: {
      region: reviewedHypotheses,
      regions: [reviewedAdditionFunctional],
      nodes: [],
      wires: [],
    },
    target: successorTransportAntecedent,
    retargets: [],
  })
  const transportFunctionalityScope = onlyNewCut(
    before,
    backward.diagram,
    successorTransportAntecedent,
  )
  const transportFunctionality = {
    scope: transportFunctionalityScope,
    body: exactOne(
      directCuts(backward.diagram, transportFunctionalityScope),
      'transport first-sum functionality body',
    ),
  }
  const transportFunctionalityAntecedent = exactOne(
    directCuts(backward.diagram, transportFunctionality.body),
    'transport first-sum functionality antecedent',
  )
  const transportFunctionalityConsequent = exactOne(
    directCuts(backward.diagram, transportFunctionalityAntecedent),
    'transport first-sum functionality consequent',
  )
  const transportFunctionalityPluses = directNodes(
    backward.diagram,
    transportFunctionalityAntecedent,
  ).filter((node) =>
    backward.diagram.nodes[node]!.kind === 'atom'
    && endpointWire(backward.diagram, node, 'head') === reviewedPlus)
  if (transportFunctionalityPluses.length !== 2) {
    throw new Error('expected two transport functionality premises')
  }
  const [
    transportFunctionalityFirst,
    transportFunctionalitySecond,
  ] = transportFunctionalityPluses
  for (const [label, outer, inner] of [
    [
      'left',
      helperClosureSuccessor!,
      endpointWire(
        backward.diagram,
        transportFunctionalityFirst!,
        'arg',
        0,
      ),
    ],
    [
      'right',
      transportRight!,
      endpointWire(
        backward.diagram,
        transportFunctionalityFirst!,
        'arg',
        1,
      ),
    ],
    [
      'derived output',
      transportSuccessorSum,
      endpointWire(
        backward.diagram,
        transportFunctionalityFirst!,
        'arg',
        2,
      ),
    ],
    [
      'supplied output',
      transportFirstSum!,
      endpointWire(
        backward.diagram,
        transportFunctionalitySecond!,
        'arg',
        2,
      ),
    ],
  ] as const) {
    backward.record(`specialize transport functionality ${label}`, {
      rule: 'wireJoin',
      input: { kind: 'iota', a: outer, b: inner },
    })
  }
  for (const premise of directNodes(
    backward.diagram,
    transportFunctionalityAntecedent,
  )) {
    backward.record(
      'discharge transport first-sum functionality premise',
      deiterationStep(
        backward.diagram,
        transportFunctionalityAntecedent,
        premise,
      ),
    )
  }
  const transportFirstSumIdentity = exactOne(
    directNodes(backward.diagram, transportFunctionalityConsequent),
    'transport first-sum identity',
  )
  backward.record('expose transport first-sum identity', {
    rule: 'doubleCutElim',
    region: transportFunctionalityAntecedent,
  })
  backward.record('finish transport first-sum functionality', {
    rule: 'doubleCutElim',
    region: transportFunctionality.scope,
  })

  const copiedPredecessorTransport = copySpecializedScope(
    helperClosureAntecedent,
    predecessorTransport,
    successorTransportAntecedent,
    [
      transportRight!,
      transportThird!,
      transportPredecessorSum,
      transportInnerSum!,
    ],
    'predecessor transport for successor closure',
  )
  const copiedPredecessorTransportAntecedent = exactOne(
    directCuts(backward.diagram, copiedPredecessorTransport.body),
    'copied predecessor transport antecedent',
  )
  const copiedPredecessorTransportConsequent = exactOne(
    directCuts(
      backward.diagram,
      copiedPredecessorTransportAntecedent,
    ),
    'copied predecessor transport consequent',
  )
  for (const premise of directNodes(
    backward.diagram,
    copiedPredecessorTransportAntecedent,
  )) {
    backward.record(
      'discharge copied predecessor transport premise',
      deiterationStep(
        backward.diagram,
        copiedPredecessorTransportAntecedent,
        premise,
      ),
    )
  }
  const copiedPredecessorTransportResults = directNodes(
    backward.diagram,
    copiedPredecessorTransportConsequent,
  ).filter((node) =>
    backward.diagram.nodes[node]!.kind === 'atom'
    && endpointWire(backward.diagram, node, 'head') === reviewedPlus)
  const predecessorOuterResult = exactOne(
    copiedPredecessorTransportResults.filter((node) =>
      endpointWire(backward.diagram, node, 'arg', 0)
        === helperClosurePredecessor),
    'predecessor outer transport result',
  )
  const predecessorFirstResult = exactOne(
    copiedPredecessorTransportResults.filter((node) =>
      node !== predecessorOuterResult),
    'predecessor first-sum transport result',
  )
  const predecessorTransportOutput = endpointWire(
    backward.diagram,
    predecessorOuterResult,
    'arg',
    2,
  )
  backward.record('expose copied predecessor transport results', {
    rule: 'doubleCutElim',
    region: copiedPredecessorTransportAntecedent,
  })
  backward.record('finish copied predecessor transport', {
    rule: 'doubleCutElim',
    region: copiedPredecessorTransport.scope,
  })

  const transportOutputSuccessor = copySpecializedScope(
    reviewedHypotheses,
    reviewedSuccessorTotal!,
    successorTransportAntecedent,
    [predecessorTransportOutput],
    'successor totality for transport output',
  )
  const transportOutputSuccessorNode = exactOne(
    directNodes(backward.diagram, transportOutputSuccessor.body).filter(
      (node) =>
        backward.diagram.nodes[node]!.kind === 'atom'
        && endpointWire(backward.diagram, node, 'head')
          === reviewedSuccessor,
    ),
    'transport output successor',
  )
  const successorTransportWitness = endpointWire(
    backward.diagram,
    transportOutputSuccessorNode,
    'arg',
    1,
  )
  backward.record('expose transport output successor', {
    rule: 'doubleCutElim',
    region: transportOutputSuccessor.scope,
  })
  backward.record('choose successor transport output witness', {
    rule: 'wireJoin',
    input: {
      kind: 'iota',
      a: successorTransportWitness,
      b: successorTransportOutput,
    },
  })

  const steppedFirstTransportResult = deriveSteppedAddition(
    transportPredecessorSum,
    transportThird!,
    predecessorTransportOutput,
    transportSuccessorSum,
    successorTransportWitness,
    'transport first-result addition step',
  )
  const steppedOuterTransportResult = deriveSteppedAddition(
    helperClosurePredecessor!,
    transportInnerSum!,
    predecessorTransportOutput,
    helperClosureSuccessor!,
    successorTransportWitness,
    'transport outer-result addition step',
  )

  const firstResultSelection = {
    region: successorTransportAntecedent,
    regions: [],
    nodes: [steppedFirstTransportResult],
    wires: [],
  } as const
  const firstResultAttachments = extractSubgraph(
    backward.diagram,
    firstResultSelection,
  ).attachments
  const firstResultBoundary = firstResultAttachments.indexOf(
    transportSuccessorSum,
  )
  if (firstResultBoundary < 0) {
    throw new Error('stepped first transport result lost first-sum boundary')
  }
  before = backward.diagram
  backward.record('retarget stepped first transport result', {
    rule: 'iteration',
    sel: firstResultSelection,
    target: successorTransportAntecedent,
    retargets: [{
      boundary: firstResultBoundary,
      identity: transportFirstSumIdentity,
      from: transportSuccessorSum,
      to: transportFirstSum!,
    }],
  })
  const retargetedFirstTransportResult = onlyNewNode(
    before,
    backward.diagram,
    successorTransportAntecedent,
  )

  backward.record(
    'discharge successor first-sum transport goal',
    deiterationStep(
      backward.diagram,
      successorTransportConsequent,
      successorFirstGoal,
    ),
  )
  backward.record(
    'discharge successor outer transport goal',
    deiterationStep(
      backward.diagram,
      successorTransportConsequent,
      successorOuterGoal,
    ),
  )
  const successorFirstPremiseSelection = {
    region: successorTransportAntecedent,
    regions: [],
    nodes: [successorFirstPremise],
    wires: [],
  } as const
  const successorFirstPremiseBoundary = extractSubgraph(
    backward.diagram,
    successorFirstPremiseSelection,
  ).attachments.indexOf(transportFirstSum!)
  if (successorFirstPremiseBoundary < 0) {
    throw new Error('successor first premise lost first-sum boundary')
  }
  const successorFirstPremiseRetargets = [{
    boundary: successorFirstPremiseBoundary,
    identity: transportFirstSumIdentity,
    from: transportSuccessorSum,
    to: transportFirstSum!,
  }] as const
  const successorFirstPremiseEvidence = findDeiterationEvidence(
    backward.diagram,
    successorFirstPremiseSelection,
    4096,
    successorFirstPremiseRetargets,
  )
  backward.record('consume successor first transport premise', {
    rule: 'deiteration',
    sel: successorFirstPremiseSelection,
    justifier: successorFirstPremiseEvidence.justifier,
    certificate: successorFirstPremiseEvidence.certificate,
    retargets: successorFirstPremiseRetargets,
  })


  void predecessorTotality
  void predecessorTransport
  void successorTransport
  void closureSuccessorPremise
  void copiedTotalityResult
  void transportSpecializedFirst
  void successorInnerPremise
  void predecessorFirstResult
  void retargetedFirstTransportResult
  void steppedOuterTransportResult
  void helperClosureConsequent
  void helperClosurePredecessor
  void helperClosureSuccessor

  return {
    name: 'associativityCarrierHereditary',
    lhs,
    rhs,
    actions: forward.actions,
    backActions: backward.actions,
  }
}
