import type {
  Diagram,
  NodeId,
  RegionId,
  WireId,
} from '../kernel/diagram/diagram'
import { IOTA, relSig, sigEquals } from '../kernel/diagram/sig'
import { findDeiterationEvidence } from '../kernel/rules/iteration'
import {
  registerTheorem,
  verifyTheory,
  type ProofContext,
  type Theory,
} from '../kernel/proof/context'
import type { Theorem } from '../kernel/proof/theorem'
import {
  emptyGraph,
  finishDiagramWithBoundary,
} from './graph'
import {
  PrimitiveStepRecorder,
  onlyNewCut,
  onlyNewNode,
  onlyNewWire,
} from './record'
import type { ArithmeticStatements } from './statements'

const UNARY = relSig([IOTA])
const BINARY = relSig([IOTA, IOTA])
const TERNARY = relSig([IOTA, IOTA, IOTA])

function directCuts(
  diagram: Diagram,
  parent: RegionId,
): readonly RegionId[] {
  return Object.entries(diagram.regions)
    .filter(([, region]) =>
      region.kind === 'cut' && region.parent === parent)
    .map(([id]) => id)
}
function directNodes(
  diagram: Diagram,
  region: RegionId,
): readonly NodeId[] {
  return Object.entries(diagram.nodes)
    .filter(([, node]) => node.region === region)
    .map(([id]) => id)
}

function scopedWires(
  diagram: Diagram,
  region: RegionId,
): readonly WireId[] {
  return Object.entries(diagram.wires)
    .filter(([, wire]) => wire.scope === region)
    .map(([id]) => id)
}

function exactOne<T>(
  values: readonly T[],
  what: string,
): T {
  if (values.length !== 1) {
    throw new Error(`expected exactly one ${what}, found ${values.length}`)
  }
  return values[0]!
}

function endpointWire(
  diagram: Diagram,
  nodeId: NodeId,
  kind: 'head' | 'arg' | 'identity',
  index?: number,
): WireId {
  return exactOne(
    Object.entries(diagram.wires)
      .filter(([, wire]) => wire.endpoints.some((endpoint) =>
        endpoint.node === nodeId
        && endpoint.port.kind === kind
        && (
          kind === 'head'
          || (
            endpoint.port.kind !== 'head'
            && endpoint.port.index === index
          )
        )))
      .map(([id]) => id),
    `${kind}${index === undefined ? '' : ` ${index}`} wire on '${nodeId}'`,
  )
}

function nodeWithHead(
  diagram: Diagram,
  region: RegionId,
  relation: WireId,
): NodeId {
  return exactOne(
    directNodes(diagram, region).filter((node) =>
      endpointWire(diagram, node, 'head') === relation),
    `atom headed by '${relation}' in '${region}'`,
  )
}

function relationWire(
  diagram: Diagram,
  scope: RegionId,
  signature: typeof UNARY,
): WireId {
  return exactOne(
    scopedWires(diagram, scope).filter((wire) =>
      sigEquals(diagram.wires[wire]!.sig, signature)),
    `relation wire in '${scope}'`,
  )
}

function deiterationStep(
  diagram: Diagram,
  region: RegionId,
  node: NodeId,
) {
  const sel = {
    region,
    regions: [],
    nodes: [node],
    wires: [],
  } as const
  const evidence = findDeiterationEvidence(diagram, sel, 4096)
  return {
    rule: 'deiteration',
    sel,
    justifier: evidence.justifier,
    certificate: evidence.certificate,
    retargets: [],
  } as const
}

function plusLeftUnit(
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
    'primitive universal body',
  )

  before = forward.diagram
  forward.record('introduce theorem-local zero relation', {
    rule: 'vacuousIntro',
    scope: primitiveScope,
    sig: UNARY,
  })
  const zero = onlyNewWire(before, forward.diagram, primitiveScope)

  before = forward.diagram
  forward.record('introduce theorem-local successor relation', {
    rule: 'vacuousIntro',
    scope: primitiveScope,
    sig: BINARY,
  })
  const successor = onlyNewWire(before, forward.diagram, primitiveScope)

  before = forward.diagram
  forward.record('introduce theorem-local addition relation', {
    rule: 'vacuousIntro',
    scope: primitiveScope,
    sig: TERNARY,
  })
  const plus = onlyNewWire(before, forward.diagram, primitiveScope)

  before = forward.diagram
  forward.record('open standing-hypothesis implication', {
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
    'theorem conclusion',
  )

  before = forward.diagram
  forward.record('insert zero anchor', {
    rule: 'atomSpawn',
    region: hypotheses,
    wire: zero,
  })
  const zeroAnchor = onlyNewNode(before, forward.diagram, hypotheses)
  const zeroValue = endpointWire(forward.diagram, zeroAnchor, 'arg', 0)

  before = forward.diagram
  forward.record('insert successor anchor', {
    rule: 'atomSpawn',
    region: hypotheses,
    wire: successor,
  })
  const successorAnchor = onlyNewNode(
    before,
    forward.diagram,
    hypotheses,
  )
  const successorInput = endpointWire(
    forward.diagram,
    successorAnchor,
    'arg',
    0,
  )
  const successorValue = endpointWire(
    forward.diagram,
    successorAnchor,
    'arg',
    1,
  )
  forward.record('attach successor anchor to zero', {
    rule: 'wireJoin',
    input: {
      kind: 'iota',
      a: zeroValue,
      b: successorInput,
    },
  })

  before = forward.diagram
  forward.record('insert addition-base anchor', {
    rule: 'atomSpawn',
    region: hypotheses,
    wire: plus,
  })
  const baseAnchor = onlyNewNode(before, forward.diagram, hypotheses)
  for (let index = 0; index < 3; index += 1) {
    forward.record(`attach addition-base argument ${index} to zero`, {
      rule: 'wireJoin',
      input: {
        kind: 'iota',
        a: zeroValue,
        b: endpointWire(forward.diagram, baseAnchor, 'arg', index),
      },
    })
  }

  before = forward.diagram
  forward.record('insert addition-step anchor', {
    rule: 'atomSpawn',
    region: hypotheses,
    wire: plus,
  })
  const stepAnchor = onlyNewNode(before, forward.diagram, hypotheses)
  forward.record('attach stepped left argument to successor', {
    rule: 'wireJoin',
    input: {
      kind: 'iota',
      a: successorValue,
      b: endpointWire(forward.diagram, stepAnchor, 'arg', 0),
    },
  })
  forward.record('attach stepped right argument to zero', {
    rule: 'wireJoin',
    input: {
      kind: 'iota',
      a: zeroValue,
      b: endpointWire(forward.diagram, stepAnchor, 'arg', 1),
    },
  })
  forward.record('attach stepped output to successor', {
    rule: 'wireJoin',
    input: {
      kind: 'iota',
      a: successorValue,
      b: endpointWire(forward.diagram, stepAnchor, 'arg', 2),
    },
  })

  before = forward.diagram
  forward.record('open left-unit universal scope', {
    rule: 'doubleCutIntro',
    sel: {
      region: conclusion,
      regions: [],
      nodes: [],
      wires: [],
    },
  })
  const claimScope = onlyNewCut(before, forward.diagram, conclusion)
  const claimBody = exactOne(
    directCuts(forward.diagram, claimScope),
    'left-unit universal body',
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
    sel: {
      region: claimBody,
      regions: [],
      nodes: [],
      wires: [],
    },
  })
  const claimAntecedent = onlyNewCut(
    before,
    forward.diagram,
    claimBody,
  )
  const claimConsequent = exactOne(
    directCuts(forward.diagram, claimAntecedent),
    'left-unit consequent',
  )

  before = forward.diagram
  forward.record('insert left-unit zero premise', {
    rule: 'atomSpawn',
    region: claimAntecedent,
    wire: zero,
  })
  const claimZeroNode = onlyNewNode(
    before,
    forward.diagram,
    claimAntecedent,
  )
  forward.record('attach left-unit zero premise', {
    rule: 'wireJoin',
    input: {
      kind: 'iota',
      a: claimZero,
      b: endpointWire(forward.diagram, claimZeroNode, 'arg', 0),
    },
  })

  before = forward.diagram
  forward.record('insert left-unit addition premise', {
    rule: 'atomSpawn',
    region: claimAntecedent,
    wire: plus,
  })
  const claimPlusNode = onlyNewNode(
    before,
    forward.diagram,
    claimAntecedent,
  )
  for (const [index, wire] of [
    [0, claimZero],
    [1, claimAddend],
    [2, claimOutput],
  ] as const) {
    forward.record(`attach left-unit addition argument ${index}`, {
      rule: 'wireJoin',
      input: {
        kind: 'iota',
        a: wire,
        b: endpointWire(forward.diagram, claimPlusNode, 'arg', index),
      },
    })
  }

  before = forward.diagram
  forward.record('insert addition-base result', {
    rule: 'atomSpawn',
    region: claimAntecedent,
    wire: plus,
  })
  const claimBase = onlyNewNode(
    before,
    forward.diagram,
    claimAntecedent,
  )
  for (const [index, wire] of [
    [0, claimZero],
    [1, claimAddend],
    [2, claimAddend],
  ] as const) {
    forward.record(`attach addition-base result argument ${index}`, {
      rule: 'wireJoin',
      input: {
        kind: 'iota',
        a: wire,
        b: endpointWire(forward.diagram, claimBase, 'arg', index),
      },
    })
  }

  before = forward.diagram
  forward.record('insert functional-addition equality', {
    rule: 'identityInsert',
    region: claimAntecedent,
    wires: [claimOutput, claimAddend],
  })
  const functionalEquality = onlyNewNode(
    before,
    forward.diagram,
    claimAntecedent,
  )
  forward.record('iterate functional-addition equality to the goal', {
    rule: 'iteration',
    sel: {
      region: claimAntecedent,
      regions: [],
      nodes: [functionalEquality],
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
  const primitiveOuter = exactOne(
    directCuts(backward.diagram, backward.diagram.root),
    'reviewed primitive scope',
  )
  const reviewedPrimitiveBody = exactOne(
    directCuts(backward.diagram, primitiveOuter),
    'reviewed primitive body',
  )
  const reviewedHypotheses = exactOne(
    directCuts(backward.diagram, reviewedPrimitiveBody),
    'reviewed theorem antecedent',
  )
  const hypothesisChildren = directCuts(
    backward.diagram,
    reviewedHypotheses,
  )
  if (hypothesisChildren.length !== 7) {
    throw new Error(
      `expected reviewed conclusion plus six quantified hypotheses, found ${hypothesisChildren.length}`,
    )
  }
  const [
    reviewedConclusion,
    zeroUnique,
    successorTotal,
    successorFunctional,
    additionBase,
    additionStep,
    additionFunctional,
  ] = hypothesisChildren
  const reviewedZero = relationWire(
    backward.diagram,
    primitiveOuter,
    UNARY,
  )
  const reviewedSuccessor = relationWire(
    backward.diagram,
    primitiveOuter,
    BINARY,
  )
  const reviewedPlus = relationWire(
    backward.diagram,
    primitiveOuter,
    TERNARY,
  )
  const existingZero = nodeWithHead(
    backward.diagram,
    reviewedHypotheses,
    reviewedZero,
  )
  const existingZeroWire = endpointWire(
    backward.diagram,
    existingZero,
    'arg',
    0,
  )
  const reviewedClaimScope = exactOne(
    directCuts(backward.diagram, reviewedConclusion!),
    'reviewed left-unit universal scope',
  )
  const reviewedClaimBody = exactOne(
    directCuts(backward.diagram, reviewedClaimScope),
    'reviewed left-unit universal body',
  )
  const reviewedClaimAntecedent = exactOne(
    directCuts(backward.diagram, reviewedClaimBody),
    'reviewed left-unit antecedent',
  )
  exactOne(
    directCuts(backward.diagram, reviewedClaimAntecedent),
    'reviewed left-unit consequent',
  )
  const reviewedClaimZero = nodeWithHead(
    backward.diagram,
    reviewedClaimAntecedent,
    reviewedZero,
  )
  const reviewedClaimPlus = nodeWithHead(
    backward.diagram,
    reviewedClaimAntecedent,
    reviewedPlus,
  )
  const reviewedClaimZeroWire = endpointWire(
    backward.diagram,
    reviewedClaimZero,
    'arg',
    0,
  )
  const reviewedClaimAddend = endpointWire(
    backward.diagram,
    reviewedClaimPlus,
    'arg',
    1,
  )
  const reviewedClaimOutput = endpointWire(
    backward.diagram,
    reviewedClaimPlus,
    'arg',
    2,
  )

  before = backward.diagram
  backward.record('copy addition base into left-unit case', {
    rule: 'iteration',
    sel: {
      region: reviewedHypotheses,
      regions: [additionBase!],
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
    'copied addition-base body',
  )
  const copiedBaseAntecedent = exactOne(
    directCuts(backward.diagram, copiedBaseBody),
    'copied addition-base antecedent',
  )
  const copiedBaseConsequent = exactOne(
    directCuts(backward.diagram, copiedBaseAntecedent),
    'copied addition-base consequent',
  )
  const copiedBaseZero = nodeWithHead(
    backward.diagram,
    copiedBaseAntecedent,
    reviewedZero,
  )
  const copiedBasePlus = nodeWithHead(
    backward.diagram,
    copiedBaseConsequent,
    reviewedPlus,
  )
  const copiedBaseZeroWire = endpointWire(
    backward.diagram,
    copiedBaseZero,
    'arg',
    0,
  )
  const copiedBaseAddend = endpointWire(
    backward.diagram,
    copiedBasePlus,
    'arg',
    1,
  )
  backward.record('specialize addition-base zero variable', {
    rule: 'wireJoin',
    input: {
      kind: 'iota',
      a: reviewedClaimZeroWire,
      b: copiedBaseZeroWire,
    },
  })
  backward.record('specialize addition-base addend variable', {
    rule: 'wireJoin',
    input: {
      kind: 'iota',
      a: reviewedClaimAddend,
      b: copiedBaseAddend,
    },
  })
  backward.record(
    'discharge copied addition-base zero premise',
    deiterationStep(
      backward.diagram,
      copiedBaseAntecedent,
      copiedBaseZero,
    ),
  )
  backward.record('expose copied addition-base result', {
    rule: 'doubleCutElim',
    region: copiedBaseAntecedent,
  })
  backward.record('finish addition-base specialization', {
    rule: 'doubleCutElim',
    region: copiedBaseScope,
  })

  before = backward.diagram
  backward.record('copy addition functionality into left-unit case', {
    rule: 'iteration',
    sel: {
      region: reviewedHypotheses,
      regions: [additionFunctional!],
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
    'copied functional-addition body',
  )
  const copiedFunctionalAntecedent = exactOne(
    directCuts(backward.diagram, copiedFunctionalBody),
    'copied functional-addition antecedent',
  )
  const copiedFunctionalConsequent = exactOne(
    directCuts(backward.diagram, copiedFunctionalAntecedent),
    'copied functional-addition consequent',
  )
  const copiedFunctionalPluses = directNodes(
    backward.diagram,
    copiedFunctionalAntecedent,
  ).filter((node) =>
    endpointWire(backward.diagram, node, 'head') === reviewedPlus)
  if (copiedFunctionalPluses.length !== 2) {
    throw new Error(
      `expected two copied functional-addition premises, found ${copiedFunctionalPluses.length}`,
    )
  }
  const [copiedFirstPlus, copiedSecondPlus] = copiedFunctionalPluses
  const copiedFunctionalEquality = exactOne(
    directNodes(backward.diagram, copiedFunctionalConsequent),
    'copied functional-addition equality',
  )
  const copiedFunctionalLeft = endpointWire(
    backward.diagram,
    copiedFirstPlus!,
    'arg',
    0,
  )
  const copiedFunctionalRight = endpointWire(
    backward.diagram,
    copiedFirstPlus!,
    'arg',
    1,
  )
  const copiedFirstOutput = endpointWire(
    backward.diagram,
    copiedFirstPlus!,
    'arg',
    2,
  )
  const copiedSecondOutput = endpointWire(
    backward.diagram,
    copiedSecondPlus!,
    'arg',
    2,
  )
  backward.record('specialize functional-addition left variable', {
    rule: 'wireJoin',
    input: {
      kind: 'iota',
      a: reviewedClaimZeroWire,
      b: copiedFunctionalLeft,
    },
  })
  backward.record('specialize functional-addition right variable', {
    rule: 'wireJoin',
    input: {
      kind: 'iota',
      a: reviewedClaimAddend,
      b: copiedFunctionalRight,
    },
  })
  backward.record('specialize functional-addition first output', {
    rule: 'wireJoin',
    input: {
      kind: 'iota',
      a: reviewedClaimOutput,
      b: copiedFirstOutput,
    },
  })
  backward.record('specialize functional-addition second output', {
    rule: 'wireJoin',
    input: {
      kind: 'iota',
      a: reviewedClaimAddend,
      b: copiedSecondOutput,
    },
  })
  backward.record(
    'discharge copied original addition result',
    deiterationStep(
      backward.diagram,
      copiedFunctionalAntecedent,
      copiedFirstPlus!,
    ),
  )
  backward.record(
    'discharge copied addition-base result',
    deiterationStep(
      backward.diagram,
      copiedFunctionalAntecedent,
      copiedSecondPlus!,
    ),
  )
  backward.record('expose functional-addition equality', {
    rule: 'doubleCutElim',
    region: copiedFunctionalAntecedent,
  })
  backward.record('finish functional-addition specialization', {
    rule: 'doubleCutElim',
    region: copiedFunctionalScope,
  })
  if (backward.diagram.nodes[copiedFunctionalEquality] === undefined) {
    throw new Error('functional-addition equality disappeared')
  }

  const uniqueBody = exactOne(
    directCuts(backward.diagram, zeroUnique!),
    'zero uniqueness body',
  )
  const uniqueAntecedent = exactOne(
    directCuts(backward.diagram, uniqueBody),
    'zero uniqueness antecedent',
  )
  const uniqueZeroNodes = directNodes(
    backward.diagram,
    uniqueAntecedent,
  )
  const uniqueVariables = scopedWires(backward.diagram, zeroUnique!)
  for (const variable of uniqueVariables) {
    backward.record('collapse zero-uniqueness variable to zero anchor', {
      rule: 'wireJoin',
      input: {
        kind: 'iota',
        a: existingZeroWire,
        b: variable,
      },
    })
  }
  for (const node of uniqueZeroNodes) {
    backward.record(
      'discharge collapsed zero-uniqueness premise',
      deiterationStep(backward.diagram, uniqueAntecedent, node),
    )
  }
  backward.record('remove discharged zero-uniqueness implication', {
    rule: 'doubleCutElim',
    region: uniqueAntecedent,
  })
  backward.record('remove discharged zero-uniqueness quantifier', {
    rule: 'doubleCutElim',
    region: zeroUnique!,
  })

  const totalBody = exactOne(
    directCuts(backward.diagram, successorTotal!),
    'successor-totality body',
  )
  const totalSuccessor = nodeWithHead(
    backward.diagram,
    totalBody,
    reviewedSuccessor,
  )
  const totalInput = endpointWire(
    backward.diagram,
    totalSuccessor,
    'arg',
    0,
  )
  backward.record('collapse successor-totality input to zero anchor', {
    rule: 'wireJoin',
    input: {
      kind: 'iota',
      a: existingZeroWire,
      b: totalInput,
    },
  })
  backward.record('expose successor anchor', {
    rule: 'doubleCutElim',
    region: successorTotal!,
  })
  const successorAnchorOutput = endpointWire(
    backward.diagram,
    totalSuccessor,
    'arg',
    1,
  )

  const functionalSuccessorBody = exactOne(
    directCuts(backward.diagram, successorFunctional!),
    'functional-successor body',
  )
  const functionalSuccessorAntecedent = exactOne(
    directCuts(backward.diagram, functionalSuccessorBody),
    'functional-successor antecedent',
  )
  const functionalSuccessorNodes = directNodes(
    backward.diagram,
    functionalSuccessorAntecedent,
  )
  const functionalSuccessorVariables = scopedWires(
    backward.diagram,
    successorFunctional!,
  )
  const functionalInput = endpointWire(
    backward.diagram,
    functionalSuccessorNodes[0]!,
    'arg',
    0,
  )
  const functionalOutputs = functionalSuccessorNodes.map((node) =>
    endpointWire(backward.diagram, node, 'arg', 1))
  for (const variable of functionalSuccessorVariables) {
    const target = variable === functionalInput
      ? existingZeroWire
      : successorAnchorOutput
    backward.record('collapse functional-successor variable to anchor', {
      rule: 'wireJoin',
      input: {
        kind: 'iota',
        a: target,
        b: variable,
      },
    })
  }
  for (const node of functionalSuccessorNodes) {
    backward.record(
      'discharge collapsed functional-successor premise',
      deiterationStep(backward.diagram, functionalSuccessorAntecedent, node),
    )
  }
  void functionalOutputs
  backward.record('remove discharged functional-successor implication', {
    rule: 'doubleCutElim',
    region: functionalSuccessorAntecedent,
  })
  backward.record('remove discharged functional-successor quantifier', {
    rule: 'doubleCutElim',
    region: successorFunctional!,
  })

  const baseBody = exactOne(
    directCuts(backward.diagram, additionBase!),
    'addition-base body',
  )
  const baseAntecedent = exactOne(
    directCuts(backward.diagram, baseBody),
    'addition-base antecedent',
  )
  const baseZero = nodeWithHead(
    backward.diagram,
    baseAntecedent,
    reviewedZero,
  )
  const basePlus = nodeWithHead(
    backward.diagram,
    exactOne(
      directCuts(backward.diagram, baseAntecedent),
      'addition-base consequent',
    ),
    reviewedPlus,
  )
  void basePlus
  const baseVariables = scopedWires(backward.diagram, additionBase!)
  for (const variable of baseVariables) {
    backward.record('collapse addition-base variable to zero anchor', {
      rule: 'wireJoin',
      input: {
        kind: 'iota',
        a: existingZeroWire,
        b: variable,
      },
    })
  }
  backward.record(
    'discharge collapsed addition-base premise',
    deiterationStep(backward.diagram, baseAntecedent, baseZero),
  )
  backward.record('expose addition-base anchor', {
    rule: 'doubleCutElim',
    region: baseAntecedent,
  })
  backward.record('finish collapsed addition-base hypothesis', {
    rule: 'doubleCutElim',
    region: additionBase!,
  })

  const stepBody = exactOne(
    directCuts(backward.diagram, additionStep!),
    'addition-step body',
  )
  const stepAntecedent = exactOne(
    directCuts(backward.diagram, stepBody),
    'addition-step antecedent',
  )
  const stepConsequent = exactOne(
    directCuts(backward.diagram, stepAntecedent),
    'addition-step consequent',
  )
  const stepPremises = directNodes(backward.diagram, stepAntecedent)
  const stepPlusPremise = exactOne(
    stepPremises.filter((node) =>
      endpointWire(backward.diagram, node, 'head') === reviewedPlus),
    'addition-step plus premise',
  )
  const stepSuccessorPremises = stepPremises.filter((node) =>
    endpointWire(backward.diagram, node, 'head') === reviewedSuccessor)
  const stepPlusResult = nodeWithHead(
    backward.diagram,
    stepConsequent,
    reviewedPlus,
  )
  const stepVariables = scopedWires(backward.diagram, additionStep!)
  const stepLeft = endpointWire(
    backward.diagram,
    stepPlusPremise,
    'arg',
    0,
  )
  const stepRight = endpointWire(
    backward.diagram,
    stepPlusPremise,
    'arg',
    1,
  )
  const stepOutput = endpointWire(
    backward.diagram,
    stepPlusPremise,
    'arg',
    2,
  )
  for (const variable of stepVariables) {
    const isSuccessor = stepSuccessorPremises.some((node) =>
      endpointWire(backward.diagram, node, 'arg', 1) === variable)
    const target = isSuccessor
      ? successorAnchorOutput
      : (
          variable === stepLeft
          || variable === stepRight
          || variable === stepOutput
            ? existingZeroWire
            : existingZeroWire
        )
    backward.record('collapse addition-step variable to anchor', {
      rule: 'wireJoin',
      input: {
        kind: 'iota',
        a: target,
        b: variable,
      },
    })
  }
  backward.record(
    'discharge collapsed addition-step plus premise',
    deiterationStep(backward.diagram, stepAntecedent, stepPlusPremise),
  )
  for (const node of stepSuccessorPremises) {
    backward.record(
      'discharge collapsed addition-step successor premise',
      deiterationStep(backward.diagram, stepAntecedent, node),
    )
  }
  backward.record('expose addition-step anchor', {
    rule: 'doubleCutElim',
    region: stepAntecedent,
  })
  backward.record('finish collapsed addition-step hypothesis', {
    rule: 'doubleCutElim',
    region: additionStep!,
  })
  if (backward.diagram.nodes[stepPlusResult] === undefined) {
    throw new Error('addition-step result disappeared')
  }

  const additionFunctionalBody = exactOne(
    directCuts(backward.diagram, additionFunctional!),
    'functional-addition body',
  )
  const additionFunctionalAntecedent = exactOne(
    directCuts(backward.diagram, additionFunctionalBody),
    'functional-addition antecedent',
  )
  const originalFunctionalPluses = directNodes(
    backward.diagram,
    additionFunctionalAntecedent,
  )
  for (const variable of scopedWires(
    backward.diagram,
    additionFunctional!,
  )) {
    backward.record('collapse functional-addition variable to zero anchor', {
      rule: 'wireJoin',
      input: {
        kind: 'iota',
        a: existingZeroWire,
        b: variable,
      },
    })
  }
  for (const node of originalFunctionalPluses) {
    backward.record(
      'discharge collapsed functional-addition premise',
      deiterationStep(backward.diagram, additionFunctionalAntecedent, node),
    )
  }
  backward.record('remove discharged functional-addition implication', {
    rule: 'doubleCutElim',
    region: additionFunctionalAntecedent,
  })
  backward.record('remove discharged functional-addition quantifier', {
    rule: 'doubleCutElim',
    region: additionFunctional!,
  })

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
