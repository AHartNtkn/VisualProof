import type { NodeId, RegionId, WireId } from '../kernel/diagram/diagram'
import { IOTA, relSig } from '../kernel/diagram/sig'
import { findDeiterationEvidence } from '../kernel/rules/iteration'
import type { ProofContext } from '../kernel/proof/context'
import { bareWireAssembly, bareWireDescription } from '../kernel/rules/identity-rules'
import type { Theorem } from '../kernel/proof/theorem'
import {
  BINARY,
  TERNARY,
  UNARY,
  directCuts,
  directNodes,
  endpointWire,
  exactOne,
  nodeWithHead,
  relationWire,
  rightIdentityCarrierContent,
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
  const zero = declareWire(graph, graph.root, UNARY)
  graph = zero.graph
  const successor = declareWire(graph, graph.root, BINARY)
  graph = successor.graph
  const plus = declareWire(graph, graph.root, TERNARY)
  graph = plus.graph

  const uniqueVariables = quantifierScope(
    graph,
    graph.root,
    'forall',
    [IOTA, IOTA],
  )
  graph = uniqueVariables.graph
  const [firstZero, secondZero] = uniqueVariables.value.variables
  const uniqueClaim = implication(graph, uniqueVariables.value.body)
  graph = uniqueClaim.graph
  graph = atom(
    graph,
    uniqueClaim.value.antecedent,
    zero.value,
    [firstZero!],
  ).graph
  graph = atom(
    graph,
    uniqueClaim.value.antecedent,
    zero.value,
    [secondZero!],
  ).graph
  graph = identity(
    graph,
    uniqueClaim.value.consequent,
    [firstZero!, secondZero!],
  ).graph

  const baseVariables = quantifierScope(
    graph,
    graph.root,
    'forall',
    [IOTA, IOTA],
  )
  graph = baseVariables.graph
  const [baseZero, baseRight] = baseVariables.value.variables
  const baseClaim = implication(graph, baseVariables.value.body)
  graph = baseClaim.graph
  graph = atom(
    graph,
    baseClaim.value.antecedent,
    zero.value,
    [baseZero!],
  ).graph
  graph = atom(
    graph,
    baseClaim.value.consequent,
    plus.value,
    [baseZero!, baseRight!, baseRight!],
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

  return finishDiagramWithBoundary(
    graph,
    [zero.value, successor.value, plus.value],
  )
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
  )
  recorder.record(label, {
    rule: 'deiteration',
    sel: selection,
    justifier: evidence.justifier,
    certificate: evidence.certificate,
  })
}

/**
 * The exact direct carrier E(a) is:
 *   forall z, Zero(z) -> Plus(a,z,a).
 *
 * This closed support theorem proves both its zero base and successor closure
 * from the ordinary standing arithmetic primitives. It deliberately owns no
 * reified property witness and contains no reference nodes.
 */
export function rightIdentityCarrierInductive(
  statements: ArithmeticStatements,
  context: ProofContext,
): Theorem {
  const lhs = finishDiagramWithBoundary(emptyGraph(), [])
  const forward = new PrimitiveStepRecorder(lhs, context)

  let before = forward.diagram
  forward.record('open carrier-support primitive scope', {
    rule: 'doubleCutIntro',
    sel: {
      region: forward.diagram.root,
      regions: [],
      nodes: [],
      wires: [],
    },
  })
  const forwardPrimitiveScope = onlyNewCut(
    before,
    forward.diagram,
    forward.diagram.root,
  )
  const forwardPrimitiveBody = exactOne(
    directCuts(forward.diagram, forwardPrimitiveScope),
    'carrier-support primitive body',
  )
  const relations: WireId[] = []
  for (const [label, sig] of [
    ['zero', UNARY],
    ['successor', BINARY],
    ['addition', TERNARY],
  ] as const) {
    before = forward.diagram
    forward.record(`introduce carrier-support ${label} relation`, {
      rule: 'vacuity',
      direction: 'insert',
      assembly: bareWireAssembly(label, forwardPrimitiveScope, sig),
    })
    relations.push(
      onlyNewWire(before, forward.diagram, forwardPrimitiveScope),
    )
  }
  const [forwardZero, forwardSuccessor, forwardPlus] =
    relations as [WireId, WireId, WireId]

  before = forward.diagram
  forward.record('open carrier-support standing implication', {
    rule: 'doubleCutIntro',
    sel: {
      region: forwardPrimitiveBody,
      regions: [],
      nodes: [],
      wires: [],
    },
  })
  const forwardHypotheses = onlyNewCut(
    before,
    forward.diagram,
    forwardPrimitiveBody,
  )
  const forwardConclusion = exactOne(
    directCuts(forward.diagram, forwardHypotheses),
    'carrier-support conclusion',
  )

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

  before = forward.diagram
  forward.record('introduce exact carrier hypotheses handle', {
    rule: 'vacuity',
    direction: 'insert',
    assembly: bareWireAssembly('exactHypotheses', forwardHypotheses, relSig([])),
  })
  const exactHypotheses = onlyNewWire(
    before,
    forward.diagram,
    forwardHypotheses,
  )
  forward.record('assert exact carrier hypotheses handle', {
    rule: 'atomSpawn',
    region: forwardHypotheses,
    wire: exactHypotheses,
  })
  forward.recordRelationJoin('ground exact zeroUnique, plusBase, and plusStep', {
    wire: exactHypotheses,
      content: exactHypothesesContent(),
      parameters: [forwardZero, forwardSuccessor, forwardPlus],
  })

  before = forward.diagram
  forward.record('open forward carrier base scope', {
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
    'forward carrier base body',
  )
  before = forward.diagram
  forward.record('introduce forward carrier base value', {
    rule: 'vacuity',
    direction: 'insert',
    assembly: bareWireAssembly('baseValue', forwardBase, IOTA),
  })
  const forwardBaseValue = onlyNewWire(
    before,
    forward.diagram,
    forwardBase,
  )
  before = forward.diagram
  forward.record('open forward carrier base implication', {
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
  exactOne(
    directCuts(forward.diagram, forwardBaseAntecedent),
    'forward empty carrier base consequent',
  )
  spawnForwardAtom(
    'forward carrier base Zero residue',
    forwardBaseAntecedent,
    forwardZero,
    [forwardBaseValue],
  )
  spawnForwardAtom(
    'forward carrier base plusBase residue',
    forwardBaseAntecedent,
    forwardPlus,
    [forwardBaseValue, forwardBaseValue, forwardBaseValue],
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
  const closureValues: WireId[] = []
  for (const label of ['predecessor', 'successor']) {
    before = forward.diagram
    forward.record(`introduce forward closure ${label}`, {
      rule: 'vacuity',
      direction: 'insert',
      assembly: bareWireAssembly('closureValue', forwardClosure, IOTA),
    })
    closureValues.push(onlyNewWire(before, forward.diagram, forwardClosure))
  }
  const [forwardPredecessor, forwardSuccessorValue] =
    closureValues as [WireId, WireId]
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
    [forwardPredecessor, forwardSuccessorValue],
  )
  spawnForwardAtom(
    'forward predecessor direct-E premise',
    forwardClosureAntecedent,
    temporaryCarrier,
    [forwardPredecessor],
  )

  before = forward.diagram
  forward.record('open forward successor E scope', {
    rule: 'doubleCutIntro',
    sel: {
      region: forwardClosureConsequent,
      regions: [],
      nodes: [],
      wires: [],
    },
  })
  const forwardSuccessorEScope = onlyNewCut(
    before,
    forward.diagram,
    forwardClosureConsequent,
  )
  const forwardSuccessorEBody = exactOne(
    directCuts(forward.diagram, forwardSuccessorEScope),
    'forward successor E body',
  )
  before = forward.diagram
  forward.record('introduce forward successor local zero', {
    rule: 'vacuity',
    direction: 'insert',
    assembly: bareWireAssembly('successorLocalZero', forwardSuccessorEScope, IOTA),
  })
  const forwardLocalZero = onlyNewWire(
    before,
    forward.diagram,
    forwardSuccessorEScope,
  )
  before = forward.diagram
  forward.record('open forward successor E implication', {
    rule: 'doubleCutIntro',
    sel: {
      region: forwardSuccessorEBody,
      regions: [],
      nodes: [],
      wires: [],
    },
  })
  const forwardSuccessorEAntecedent = onlyNewCut(
    before,
    forward.diagram,
    forwardSuccessorEBody,
  )
  exactOne(
    directCuts(forward.diagram, forwardSuccessorEAntecedent),
    'forward empty successor E goal',
  )
  spawnForwardAtom(
    'forward successor local Zero residue',
    forwardSuccessorEAntecedent,
    forwardZero,
    [forwardLocalZero],
  )
  spawnForwardAtom(
    'forward predecessor Plus residue',
    forwardSuccessorEAntecedent,
    forwardPlus,
    [forwardPredecessor, forwardLocalZero, forwardPredecessor],
  )
  spawnForwardAtom(
    'forward successor Plus residue',
    forwardSuccessorEAntecedent,
    forwardPlus,
    [forwardSuccessorValue, forwardLocalZero, forwardSuccessorValue],
  )
  forward.recordRelationJoin('ground temporary carrier directly to E', {
    wire: temporaryCarrier,
      content: rightIdentityCarrierContent(),
      parameters: [forwardZero, forwardPlus],
  })

  const rhs = statements.rightIdentityCarrierInductive
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
  const zero = relationWire(backward.diagram, primitiveScope, UNARY)
  const successor = relationWire(backward.diagram, primitiveScope, BINARY)
  const plus = relationWire(backward.diagram, primitiveScope, TERNARY)
  const conclusion = exactOne(
    hypothesisChildren.filter((region) =>
      scopedWires(backward.diagram, region).length === 0),
    'carrier-support conclusion',
  )
  const binaryHypotheses = hypothesisChildren.filter((region) =>
    scopedWires(backward.diagram, region).length === 2)
  const zeroPremiseCount = (region: RegionId) => {
    const body = exactOne(
      directCuts(backward.diagram, region),
      'binary hypothesis body',
    )
    const antecedent = exactOne(
      directCuts(backward.diagram, body),
      'binary hypothesis antecedent',
    )
    return directNodes(backward.diagram, antecedent).filter((node) =>
      backward.diagram.nodes[node]!.kind === 'atom'
      && endpointWire(backward.diagram, node, 'head') === zero)
      .length
  }
  const zeroUnique = exactOne(
    binaryHypotheses.filter((region) => zeroPremiseCount(region) === 2),
    'zeroUnique hypothesis',
  )
  const additionBase = exactOne(
    binaryHypotheses.filter((region) => zeroPremiseCount(region) === 1),
    'plusBase hypothesis',
  )
  const additionStep = exactOne(
    hypothesisChildren.filter((region) =>
      scopedWires(backward.diagram, region).length === 5),
    'plusStep hypothesis',
  )

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

  const deriveZeroIdentity = (
    targetRegion: RegionId,
    left: WireId,
    right: WireId,
    label: string,
  ): NodeId => {
    const prior = backward.diagram
    backward.record(`copy zero uniqueness for ${label}`, {
      rule: 'iteration',
      sel: {
        region: hypotheses,
        regions: [zeroUnique],
        nodes: [],
        wires: [],
      },
      target: targetRegion,
      })
    const copiedScope = onlyNewCut(prior, backward.diagram, targetRegion)
    const copiedBody = exactOne(
      directCuts(backward.diagram, copiedScope),
      `${label} uniqueness body`,
    )
    const copiedAntecedent = exactOne(
      directCuts(backward.diagram, copiedBody),
      `${label} uniqueness antecedent`,
    )
    const copiedConsequent = exactOne(
      directCuts(backward.diagram, copiedAntecedent),
      `${label} uniqueness consequent`,
    )
    const variables = scopedWires(backward.diagram, copiedScope)
    for (const [target, variable] of [
      [left, variables[0]!],
      [right, variables[1]!],
    ] as const) {
      backward.record(`specialize ${label} uniqueness`, {
        rule: 'wireJoin',
        input: { a: target, b: variable },
      })
    }
    for (const node of directNodes(backward.diagram, copiedAntecedent)) {
      deiterateNode(
        backward,
        `discharge ${label} zero premise`,
        copiedAntecedent,
        node,
      )
    }
    const identity = exactOne(
      directNodes(backward.diagram, copiedConsequent),
      `${label} identity`,
    )
    backward.record(`expose ${label} identity`, {
      rule: 'doubleCutElim',
      region: copiedAntecedent,
    })
    backward.record(`finish ${label} uniqueness`, {
      rule: 'doubleCutElim',
      region: copiedScope,
    })
    return identity
  }

  const baseEScope = exactOne(
    directCuts(backward.diagram, baseConditionConsequent),
    'carrier-support base E scope',
  )
  const baseEBody = exactOne(
    directCuts(backward.diagram, baseEScope),
    'carrier-support base E body',
  )
  const baseEAntecedent = exactOne(
    directCuts(backward.diagram, baseEBody),
    'carrier-support base E antecedent',
  )
  const baseEConsequent = exactOne(
    directCuts(backward.diagram, baseEAntecedent),
    'carrier-support base E consequent',
  )
  const baseLocalZero = exactOne(
    scopedWires(backward.diagram, baseEScope),
    'carrier-support base local zero',
  )
  const baseLocalZeroNode = exactOne(
    directNodes(backward.diagram, baseEAntecedent).filter((node) =>
      endpointWire(backward.diagram, node, 'head') === zero),
    'carrier-support local Zero',
  )
  const baseLocalPlusNode = exactOne(
    directNodes(backward.diagram, baseEConsequent).filter((node) =>
      endpointWire(backward.diagram, node, 'head') === plus),
    'carrier-support local Plus',
  )
  const baseLocalIdentity = deriveZeroIdentity(
    baseEAntecedent,
    baseValue,
    baseLocalZero,
    'carrier-base local',
  )

  before = backward.diagram
  backward.record('copy plusBase into carrier-base local case', {
    rule: 'iteration',
    sel: {
      region: hypotheses,
      regions: [additionBase],
      nodes: [],
      wires: [],
    },
    target: baseConditionAntecedent,
  })
  const copiedBaseScope = onlyNewCut(
    before,
    backward.diagram,
    baseConditionAntecedent,
  )
  const copiedBaseBody = exactOne(
    directCuts(backward.diagram, copiedBaseScope),
    'copied carrier-base plusBase body',
  )
  const copiedBaseAntecedent = exactOne(
    directCuts(backward.diagram, copiedBaseBody),
    'copied carrier-base plusBase antecedent',
  )
  const copiedBaseConsequent = exactOne(
    directCuts(backward.diagram, copiedBaseAntecedent),
    'copied carrier-base plusBase consequent',
  )
  const copiedBaseZeroNode = nodeWithHead(
    backward.diagram,
    copiedBaseAntecedent,
    zero,
  )
  const copiedBasePlus = nodeWithHead(
    backward.diagram,
    copiedBaseConsequent,
    plus,
  )
  for (const variable of scopedWires(backward.diagram, copiedBaseScope)) {
    backward.record('specialize carrier-base plusBase at supplied zero', {
      rule: 'wireJoin',
      input: { a: baseValue, b: variable },
    })
  }
  deiterateNode(
    backward,
    'discharge copied carrier-base plusBase Zero',
    copiedBaseAntecedent,
    copiedBaseZeroNode,
  )
  backward.record('expose copied carrier-base plusBase result', {
    rule: 'doubleCutElim',
    region: copiedBaseAntecedent,
  })
  backward.record('finish carrier-base plusBase specialization', {
    rule: 'doubleCutElim',
    region: copiedBaseScope,
  })

  // Substitution is the derivation (no retargets). The consequent keeps a
  // plain copy of the equality; severing the local zero so the antecedent
  // identity keeps one co-scoped end lands the local Plus on the supplied
  // zero, where it discharges exactly. The consumed antecedent identity is
  // re-derived while the local Zero hypothesis still stands, and that
  // hypothesis finally erases (backward erasure at the negative antecedent
  // reads in reverse as hypothesis insertion).
  backward.record('copy carrier-base local equality into consequent', {
    rule: 'iteration',
    sel: {
      region: baseEAntecedent,
      regions: [],
      nodes: [baseLocalIdentity],
      wires: [],
    },
    target: baseEConsequent,
  })
  backward.record('land the carrier-base local Plus on the supplied zero', {
    rule: 'wireSever',
    input: {
      wire: baseLocalZero,
      keep: backward.diagram.wires[baseLocalZero]!.endpoints
        .filter((endpoint) =>
          endpoint.node !== baseLocalIdentity
          && endpoint.node !== baseLocalPlusNode),
      scope: baseEAntecedent,
    },
  })
  deiterateNode(
    backward,
    'discharge carrier-base local Plus',
    baseEConsequent,
    baseLocalPlusNode,
  )
  deriveZeroIdentity(
    baseEAntecedent,
    baseValue,
    baseLocalZero,
    'carrier-base restored',
  )
  backward.record('erase the carrier-base local Zero hypothesis', {
    rule: 'erasure',
    sel: {
      region: baseEAntecedent,
      regions: [],
      nodes: [baseLocalZeroNode],
      wires: [],
    },
  })
  backward.record('close carrier-base local equality implication', {
    rule: 'theorem',
    name: 'ordinaryEqualityContradiction',
    direction: 'reverse',
    at: {
      sel: {
        region: baseEBody,
        regions: [baseEAntecedent],
        nodes: [],
        wires: [],
      },
      args: [baseValue, baseLocalZero],
    },
  })
  backward.record('remove carrier-base local zero binder', {
    rule: 'vacuity',
    direction: 'delete',
    assembly: bareWireDescription(backward.diagram, baseLocalZero),
  })
  backward.record('eliminate proved carrier-base E', {
    rule: 'doubleCutElim',
    region: baseEScope,
  })
  void baseZero
  void copiedBasePlus

  const closureBody = exactOne(
    directCuts(backward.diagram, closureCondition),
    'carrier-support closure body',
  )
  const closureAntecedent = exactOne(
    directCuts(backward.diagram, closureBody),
    'carrier-support closure antecedent',
  )
  const closureConsequent = exactOne(
    directCuts(backward.diagram, closureAntecedent)
      .filter((region) =>
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
    'carrier-support closure Succ',
  )
  const predecessorE = exactOne(
    directCuts(backward.diagram, closureAntecedent)
      .filter((region) => region !== closureConsequent),
    'carrier-support predecessor E',
  )
  const successorEScope = exactOne(
    directCuts(backward.diagram, closureConsequent),
    'carrier-support successor E scope',
  )
  const successorEBody = exactOne(
    directCuts(backward.diagram, successorEScope),
    'carrier-support successor E body',
  )
  const successorEAntecedent = exactOne(
    directCuts(backward.diagram, successorEBody),
    'carrier-support successor E antecedent',
  )
  const successorEConsequent = exactOne(
    directCuts(backward.diagram, successorEAntecedent),
    'carrier-support successor E consequent',
  )
  const successorLocalZero = exactOne(
    scopedWires(backward.diagram, successorEScope),
    'carrier-support successor local zero',
  )
  const successorLocalZeroNode = exactOne(
    directNodes(backward.diagram, successorEAntecedent).filter((node) =>
      endpointWire(backward.diagram, node, 'head') === zero),
    'carrier-support successor local Zero',
  )
  const successorGoal = exactOne(
    directNodes(backward.diagram, successorEConsequent).filter((node) =>
      endpointWire(backward.diagram, node, 'head') === plus),
    'carrier-support successor Plus goal',
  )

  before = backward.diagram
  backward.record('copy predecessor E into successor E', {
    rule: 'iteration',
    sel: {
      region: closureAntecedent,
      regions: [predecessorE],
      nodes: [],
      wires: [],
    },
    target: successorEAntecedent,
  })
  const copiedPredecessorE = onlyNewCut(
    before,
    backward.diagram,
    successorEAntecedent,
  )
  const copiedPredecessorZero = exactOne(
    scopedWires(backward.diagram, copiedPredecessorE),
    'copied predecessor local zero',
  )
  backward.record('specialize predecessor E at successor local zero', {
    rule: 'wireJoin',
    input: {
      a: successorLocalZero,
      b: copiedPredecessorZero,
    },
  })
  const copiedPredecessorBody = exactOne(
    directCuts(backward.diagram, copiedPredecessorE),
    'copied predecessor E body',
  )
  const copiedPredecessorAntecedent = exactOne(
    directCuts(backward.diagram, copiedPredecessorBody),
    'copied predecessor E antecedent',
  )
  const copiedPredecessorConsequent = exactOne(
    directCuts(backward.diagram, copiedPredecessorAntecedent),
    'copied predecessor E consequent',
  )
  const copiedPredecessorZeroNode = exactOne(
    directNodes(backward.diagram, copiedPredecessorAntecedent),
    'copied predecessor Zero',
  )
  const copiedPredecessorPlus = exactOne(
    directNodes(backward.diagram, copiedPredecessorConsequent),
    'copied predecessor Plus',
  )
  deiterateNode(
    backward,
    'discharge copied predecessor Zero',
    copiedPredecessorAntecedent,
    copiedPredecessorZeroNode,
  )
  backward.record('expose predecessor Plus at successor zero', {
    rule: 'doubleCutElim',
    region: copiedPredecessorAntecedent,
  })
  backward.record('finish predecessor E specialization', {
    rule: 'doubleCutElim',
    region: copiedPredecessorE,
  })

  before = backward.diagram
  backward.record('copy addition step into successor E', {
    rule: 'iteration',
    sel: {
      region: hypotheses,
      regions: [additionStep],
      nodes: [],
      wires: [],
    },
    target: successorEAntecedent,
  })
  const copiedStepScope = onlyNewCut(
    before,
    backward.diagram,
    successorEAntecedent,
  )
  const copiedStepBody = exactOne(
    directCuts(backward.diagram, copiedStepScope),
    'copied carrier-support step body',
  )
  const copiedStepAntecedent = exactOne(
    directCuts(backward.diagram, copiedStepBody),
    'copied carrier-support step antecedent',
  )
  const copiedStepConsequent = exactOne(
    directCuts(backward.diagram, copiedStepAntecedent),
    'copied carrier-support step consequent',
  )
  const copiedStepPremises = directNodes(
    backward.diagram,
    copiedStepAntecedent,
  )
  const copiedStepPlus = exactOne(
    copiedStepPremises.filter((node) =>
      endpointWire(backward.diagram, node, 'head') === plus),
    'copied carrier-support step Plus',
  )
  const copiedStepSuccessors = copiedStepPremises.filter((node) =>
    endpointWire(backward.diagram, node, 'head') === successor)
  if (copiedStepSuccessors.length !== 2) {
    throw new Error('expected two copied carrier-support successors')
  }
  const copiedStepResult = exactOne(
    directNodes(backward.diagram, copiedStepConsequent),
    'copied carrier-support step result',
  )
  const copiedLeft = endpointWire(
    backward.diagram,
    copiedStepPlus,
    'arg',
    0,
  )
  const copiedRight = endpointWire(
    backward.diagram,
    copiedStepPlus,
    'arg',
    1,
  )
  const copiedOutput = endpointWire(
    backward.diagram,
    copiedStepPlus,
    'arg',
    2,
  )
  const copiedLeftSuccessor = exactOne(
    copiedStepSuccessors.filter((node) =>
      endpointWire(backward.diagram, node, 'arg', 0) === copiedLeft),
    'copied carrier-support left successor',
  )
  const copiedOutputSuccessor = exactOne(
    copiedStepSuccessors.filter((node) => node !== copiedLeftSuccessor),
    'copied carrier-support output successor',
  )
  for (const [label, outer, inner] of [
    ['left', predecessor, copiedLeft],
    ['right', successorLocalZero, copiedRight],
    ['output', predecessor, copiedOutput],
    [
      'left successor',
      successorValue,
      endpointWire(backward.diagram, copiedLeftSuccessor, 'arg', 1),
    ],
    [
      'output successor',
      successorValue,
      endpointWire(backward.diagram, copiedOutputSuccessor, 'arg', 1),
    ],
  ] as const) {
    backward.record(`specialize carrier-support step ${label}`, {
      rule: 'wireJoin',
      input: { a: outer, b: inner },
    })
  }
  for (const node of [copiedStepPlus, ...copiedStepSuccessors]) {
    deiterateNode(
      backward,
      'discharge copied carrier-support step premise',
      copiedStepAntecedent,
      node,
    )
  }
  backward.record('expose carrier-support successor Plus', {
    rule: 'doubleCutElim',
    region: copiedStepAntecedent,
  })
  backward.record('finish carrier-support addition-step specialization', {
    rule: 'doubleCutElim',
    region: copiedStepScope,
  })
  deiterateNode(
    backward,
    'discharge carrier-support successor E goal',
    successorEConsequent,
    successorGoal,
  )
  void closureSuccessor
  void successorLocalZeroNode
  void copiedPredecessorPlus
  void copiedStepResult

  return {
    name: 'rightIdentityCarrierInductive',
    lhs,
    rhs,
    actions: forward.actions,
    backActions: backward.actions,
  }
}
