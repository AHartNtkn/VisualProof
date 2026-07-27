import { relSig } from '../kernel/diagram/sig'
import {
  registerTheorem,
  verifyTheory,
  type ProofContext,
  type Theory,
} from '../kernel/proof/context'
import type { Theorem } from '../kernel/proof/theorem'
import {
  BINARY,
  TERNARY,
  UNARY,
  deiterationSelectionStep,
  deiterationStep,
  directCuts,
  directNodes,
  endpointWire,
  exactOne,
  introducedContentSelection,
  nodeWithHead,
  relationApplicationContent,
  relationWire,
  scopedWires,
} from './arithmetic-support'
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
import { natRelation } from './naturals'
import type { ArithmeticStatements } from './statements'

function oneIsNat(
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
  const anchorZeroValue = endpointWire(
    forward.diagram,
    zeroAnchor,
    'arg',
    0,
  )

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
  const anchorSuccessorInput = endpointWire(
    forward.diagram,
    successorAnchor,
    'arg',
    0,
  )
  const anchorSuccessorValue = endpointWire(
    forward.diagram,
    successorAnchor,
    'arg',
    1,
  )
  forward.record('attach successor anchor to zero', {
    rule: 'wireJoin',
    input: {
      kind: 'iota',
      a: anchorZeroValue,
      b: anchorSuccessorInput,
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
        a: anchorZeroValue,
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
      a: anchorSuccessorValue,
      b: endpointWire(forward.diagram, stepAnchor, 'arg', 0),
    },
  })
  forward.record('attach stepped right argument to zero', {
    rule: 'wireJoin',
    input: {
      kind: 'iota',
      a: anchorZeroValue,
      b: endpointWire(forward.diagram, stepAnchor, 'arg', 1),
    },
  })
  forward.record('attach stepped output to successor', {
    rule: 'wireJoin',
    input: {
      kind: 'iota',
      a: anchorSuccessorValue,
      b: endpointWire(forward.diagram, stepAnchor, 'arg', 2),
    },
  })

  before = forward.diagram
  forward.record('insert cited zero witness', {
    rule: 'atomSpawn',
    region: hypotheses,
    wire: zero,
  })
  const citedZero = onlyNewNode(before, forward.diagram, hypotheses)
  const zeroValue = endpointWire(forward.diagram, citedZero, 'arg', 0)

  before = forward.diagram
  forward.record('introduce temporary zero-Nat proposition', {
    rule: 'vacuousIntro',
    scope: hypotheses,
    sig: relSig([]),
  })
  const temporaryZeroNat = onlyNewWire(
    before,
    forward.diagram,
    hypotheses,
  )
  before = forward.diagram
  forward.record('insert temporary zero-Nat assertion', {
    rule: 'atomSpawn',
    region: hypotheses,
    wire: temporaryZeroNat,
  })
  onlyNewNode(before, forward.diagram, hypotheses)
  before = forward.diagram
  forward.record('ground zero Nat on the supplied primitives', {
    rule: 'wireJoin',
    input: {
      kind: 'relation',
      wire: temporaryZeroNat,
      content: natRelation(),
      parameters: [zero, successor, zeroValue],
    },
  })
  const zeroNatMaterial = introducedContentSelection(
    before,
    forward.diagram,
    hypotheses,
  )
  before = forward.diagram
  forward.record('fold the grounded zero Nat result', {
    rule: 'fold',
    occurrence: zeroNatMaterial,
    args: [zero, successor, zeroValue],
    defId: 'nat',
  })
  onlyNewNode(before, forward.diagram, hypotheses)

  before = forward.diagram
  forward.record('insert cited successor witness', {
    rule: 'atomSpawn',
    region: hypotheses,
    wire: successor,
  })
  const citedSuccessor = onlyNewNode(
    before,
    forward.diagram,
    hypotheses,
  )
  const successorInput = endpointWire(
    forward.diagram,
    citedSuccessor,
    'arg',
    0,
  )
  const successorValue = endpointWire(
    forward.diagram,
    citedSuccessor,
    'arg',
    1,
  )
  forward.record('attach cited successor input to cited zero', {
    rule: 'wireJoin',
    input: {
      kind: 'iota',
      a: zeroValue,
      b: successorInput,
    },
  })

  before = forward.diagram
  forward.record('introduce temporary successor-Nat proposition', {
    rule: 'vacuousIntro',
    scope: hypotheses,
    sig: relSig([]),
  })
  const temporarySuccessorNat = onlyNewWire(
    before,
    forward.diagram,
    hypotheses,
  )
  before = forward.diagram
  forward.record('insert temporary successor-Nat assertion', {
    rule: 'atomSpawn',
    region: hypotheses,
    wire: temporarySuccessorNat,
  })
  onlyNewNode(before, forward.diagram, hypotheses)
  before = forward.diagram
  forward.record('ground successor Nat on the supplied primitives', {
    rule: 'wireJoin',
    input: {
      kind: 'relation',
      wire: temporarySuccessorNat,
      content: natRelation(),
      parameters: [zero, successor, successorValue],
    },
  })
  const successorNatMaterial = introducedContentSelection(
    before,
    forward.diagram,
    hypotheses,
  )
  before = forward.diagram
  forward.record('fold the grounded successor Nat result', {
    rule: 'fold',
    occurrence: successorNatMaterial,
    args: [zero, successor, successorValue],
    defId: 'nat',
  })
  const successorNat = onlyNewNode(
    before,
    forward.diagram,
    hypotheses,
  )

  for (const [label, node] of [
    ['zero evidence', citedZero],
    ['successor evidence', citedSuccessor],
    ['successor Nat evidence', successorNat],
  ] as const) {
    forward.record(`iterate ${label} into one-is-Nat conclusion`, {
      rule: 'iteration',
      sel: {
        region: hypotheses,
        regions: [],
        nodes: [node],
        wires: [],
      },
      target: conclusion,
      retargets: [],
    })
  }

  const rhs = statements.oneIsNat
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
    'reviewed standing-hypothesis antecedent',
  )
  const reviewedChildren = directCuts(
    backward.diagram,
    reviewedHypotheses,
  )
  if (reviewedChildren.length !== 7) {
    throw new Error(
      `expected reviewed conclusion plus six hypotheses, found ${reviewedChildren.length}`,
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
  ] = reviewedChildren
  const reviewedZero = relationWire(
    backward.diagram,
    reviewedPrimitiveScope,
    UNARY,
  )
  const reviewedSuccessor = relationWire(
    backward.diagram,
    reviewedPrimitiveScope,
    BINARY,
  )
  const reviewedPlus = relationWire(
    backward.diagram,
    reviewedPrimitiveScope,
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

  before = backward.diagram
  backward.record('cite zeroIsNat into one-is-Nat hypotheses', {
    rule: 'theorem',
    name: 'zeroIsNat',
    direction: 'forward',
    at: {
      sel: {
        region: reviewedHypotheses,
        regions: [],
        nodes: [],
        wires: [],
      },
      args: [],
    },
  })
  const zeroCitationScope = onlyNewCut(
    before,
    backward.diagram,
    reviewedHypotheses,
  )
  const zeroCitationBody = exactOne(
    directCuts(backward.diagram, zeroCitationScope),
    'zero citation primitive body',
  )
  const zeroCitationAntecedent = exactOne(
    directCuts(backward.diagram, zeroCitationBody),
    'zero citation antecedent',
  )
  const zeroCitationChildren = directCuts(
    backward.diagram,
    zeroCitationAntecedent,
  )
  if (zeroCitationChildren.length !== 7) {
    throw new Error(
      `expected zero citation conclusion plus six hypotheses, found ${zeroCitationChildren.length}`,
    )
  }
  const [zeroCitationConclusion, ...zeroCitationHypotheses] =
    zeroCitationChildren
  const citedZeroRelation = relationWire(
    backward.diagram,
    zeroCitationScope,
    UNARY,
  )
  const citedSuccessorRelation = relationWire(
    backward.diagram,
    zeroCitationScope,
    BINARY,
  )
  const citedPlusRelation = relationWire(
    backward.diagram,
    zeroCitationScope,
    TERNARY,
  )
  const zeroCitationConclusionNodes = directNodes(
    backward.diagram,
    zeroCitationConclusion!,
  )
  const extractedZero = exactOne(
    zeroCitationConclusionNodes.filter((node) =>
      backward.diagram.nodes[node]!.kind === 'atom'),
    'cited zero conclusion atom',
  )
  const citedZeroNat = exactOne(
    zeroCitationConclusionNodes.filter((node) =>
      backward.diagram.nodes[node]!.kind === 'ref'),
    'cited zero conclusion Nat',
  )
  const extractedZeroValue = endpointWire(
    backward.diagram,
    extractedZero,
    'arg',
    0,
  )
  backward.record('unfold the cited zero Nat result', {
    rule: 'unfold',
    nodeId: citedZeroNat,
  })
  for (const [label, outer, inner, signature] of [
    ['zero', reviewedZero, citedZeroRelation, UNARY],
    ['successor', reviewedSuccessor, citedSuccessorRelation, BINARY],
    ['addition', reviewedPlus, citedPlusRelation, TERNARY],
  ] as const) {
    backward.record(`ground cited ${label} primitive`, {
      rule: 'wireJoin',
      input: {
        kind: 'relation',
        wire: inner,
        content: relationApplicationContent(signature),
        parameters: [outer],
      },
    })
  }
  const citedZeroNatScope = exactOne(
    directCuts(backward.diagram, zeroCitationConclusion!),
    'grounded cited-zero Nat scope',
  )
  before = backward.diagram
  backward.record('fold the grounded cited zero Nat result', {
    rule: 'fold',
    occurrence: {
      region: zeroCitationConclusion!,
      regions: [citedZeroNatScope],
      nodes: [],
      wires: [],
    },
    args: [reviewedZero, reviewedSuccessor, extractedZeroValue],
    defId: 'nat',
  })
  const extractedZeroNat = onlyNewNode(
    before,
    backward.diagram,
    zeroCitationConclusion!,
  )
  const zeroCitationExisting = nodeWithHead(
    backward.diagram,
    zeroCitationAntecedent,
    reviewedZero,
  )
  const zeroCitationExistingWire = endpointWire(
    backward.diagram,
    zeroCitationExisting,
    'arg',
    0,
  )
  backward.record(
    'remove cited existential-zero hypothesis',
    deiterationSelectionStep(backward.diagram, {
      region: zeroCitationAntecedent,
      regions: [],
      nodes: [zeroCitationExisting],
      wires: [zeroCitationExistingWire],
    }),
  )
  for (const citedHypothesis of zeroCitationHypotheses) {
    backward.record(
      'remove copied zeroIsNat standing hypothesis',
      deiterationSelectionStep(backward.diagram, {
        region: zeroCitationAntecedent,
        regions: [citedHypothesis],
        nodes: [],
        wires: [],
      }),
    )
  }
  backward.record('expose cited zeroIsNat conclusion', {
    rule: 'doubleCutElim',
    region: zeroCitationAntecedent,
  })
  backward.record('remove cited zeroIsNat primitive scope', {
    rule: 'doubleCutElim',
    region: zeroCitationScope,
  })

  before = backward.diagram
  backward.record('cite succNat into one-is-Nat hypotheses', {
    rule: 'theorem',
    name: 'succNat',
    direction: 'forward',
    at: {
      sel: {
        region: reviewedHypotheses,
        regions: [],
        nodes: [],
        wires: [],
      },
      args: [],
    },
  })
  const successorCitationScope = onlyNewCut(
    before,
    backward.diagram,
    reviewedHypotheses,
  )
  const successorCitationBody = exactOne(
    directCuts(backward.diagram, successorCitationScope),
    'successor citation primitive body',
  )
  const successorCitationAntecedent = exactOne(
    directCuts(backward.diagram, successorCitationBody),
    'successor citation antecedent',
  )
  const successorCitationChildren = directCuts(
    backward.diagram,
    successorCitationAntecedent,
  )
  if (successorCitationChildren.length !== 7) {
    throw new Error(
      `expected successor citation conclusion plus six hypotheses, found ${successorCitationChildren.length}`,
    )
  }
  const [successorCitationConclusion, ...successorCitationHypotheses] =
    successorCitationChildren
  const citedRuleScope = exactOne(
    directCuts(backward.diagram, successorCitationConclusion!),
    'cited successor-closure universal scope',
  )
  const citedRuleBody = exactOne(
    directCuts(backward.diagram, citedRuleScope),
    'cited successor-closure universal body',
  )
  const citedRuleAntecedent = exactOne(
    directCuts(backward.diagram, citedRuleBody),
    'cited successor-closure antecedent',
  )
  const citedRuleConsequent = exactOne(
    directCuts(backward.diagram, citedRuleAntecedent),
    'cited successor-closure consequent',
  )
  const citedSuccessorZero = relationWire(
    backward.diagram,
    successorCitationScope,
    UNARY,
  )
  const citedSuccessorSuccessor = relationWire(
    backward.diagram,
    successorCitationScope,
    BINARY,
  )
  const citedSuccessorPlus = relationWire(
    backward.diagram,
    successorCitationScope,
    TERNARY,
  )
  const citedRulePremisesBeforeGrounding = directNodes(
    backward.diagram,
    citedRuleAntecedent,
  )
  const citedRuleNatPremiseBeforeGrounding = exactOne(
    citedRulePremisesBeforeGrounding.filter((node) =>
      backward.diagram.nodes[node]!.kind === 'ref'),
    'ungrounded cited successor rule Nat premise',
  )
  const citedRuleNatResultBeforeGrounding = exactOne(
    directNodes(backward.diagram, citedRuleConsequent)
      .filter((node) => backward.diagram.nodes[node]!.kind === 'ref'),
    'ungrounded cited successor rule Nat result',
  )
  const citedRulePredecessorNatValue = endpointWire(
    backward.diagram,
    citedRuleNatPremiseBeforeGrounding,
    'arg',
    2,
  )
  const citedRuleSuccessorNatValue = endpointWire(
    backward.diagram,
    citedRuleNatResultBeforeGrounding,
    'arg',
    2,
  )
  before = backward.diagram
  backward.record('unfold the cited successor-rule Nat premise', {
    rule: 'unfold',
    nodeId: citedRuleNatPremiseBeforeGrounding,
  })
  const citedPremiseNatScope = onlyNewCut(
    before,
    backward.diagram,
    citedRuleAntecedent,
  )
  before = backward.diagram
  backward.record('unfold the cited successor-rule Nat result', {
    rule: 'unfold',
    nodeId: citedRuleNatResultBeforeGrounding,
  })
  const citedResultNatScope = onlyNewCut(
    before,
    backward.diagram,
    citedRuleConsequent,
  )

  for (const [label, outer, inner, signature] of [
    ['zero', reviewedZero, citedSuccessorZero, UNARY],
    ['successor', reviewedSuccessor, citedSuccessorSuccessor, BINARY],
    ['addition', reviewedPlus, citedSuccessorPlus, TERNARY],
  ] as const) {
    backward.record(`ground succNat ${label} primitive`, {
      rule: 'wireJoin',
      input: {
        kind: 'relation',
        wire: inner,
        content: relationApplicationContent(signature),
        parameters: [outer],
      },
    })
  }
  before = backward.diagram
  backward.record('fold the grounded cited successor-rule Nat premise', {
    rule: 'fold',
    occurrence: {
      region: citedRuleAntecedent,
      regions: [citedPremiseNatScope],
      nodes: [],
      wires: [],
    },
    args: [
      reviewedZero,
      reviewedSuccessor,
      citedRulePredecessorNatValue,
    ],
    defId: 'nat',
  })
  const citedRuleNatPremise = onlyNewNode(
    before,
    backward.diagram,
    citedRuleAntecedent,
  )
  before = backward.diagram
  backward.record('fold the grounded cited successor-rule Nat result', {
    rule: 'fold',
    occurrence: {
      region: citedRuleConsequent,
      regions: [citedResultNatScope],
      nodes: [],
      wires: [],
    },
    args: [
      reviewedZero,
      reviewedSuccessor,
      citedRuleSuccessorNatValue,
    ],
    defId: 'nat',
  })
  const citedRuleNatResult = onlyNewNode(
    before,
    backward.diagram,
    citedRuleConsequent,
  )
  const successorCitationExisting = nodeWithHead(
    backward.diagram,
    successorCitationAntecedent,
    reviewedZero,
  )
  const successorCitationExistingWire = endpointWire(
    backward.diagram,
    successorCitationExisting,
    'arg',
    0,
  )
  const citedRuleSuccessorPremise = nodeWithHead(
    backward.diagram,
    citedRuleAntecedent,
    reviewedSuccessor,
  )
  backward.record(
    'remove cited succNat existential-zero hypothesis',
    deiterationSelectionStep(backward.diagram, {
      region: successorCitationAntecedent,
      regions: [],
      nodes: [successorCitationExisting],
      wires: [successorCitationExistingWire],
    }),
  )
  for (const citedHypothesis of successorCitationHypotheses) {
    backward.record(
      'remove copied succNat standing hypothesis',
      deiterationSelectionStep(backward.diagram, {
        region: successorCitationAntecedent,
        regions: [citedHypothesis],
        nodes: [],
        wires: [],
      }),
    )
  }
  backward.record('expose cited succNat conclusion', {
    rule: 'doubleCutElim',
    region: successorCitationAntecedent,
  })
  backward.record('remove cited succNat primitive scope', {
    rule: 'doubleCutElim',
    region: successorCitationScope,
  })

  before = backward.diagram
  backward.record('copy successor totality for the cited zero', {
    rule: 'iteration',
    sel: {
      region: reviewedHypotheses,
      regions: [successorTotal!],
      nodes: [],
      wires: [],
    },
    target: reviewedHypotheses,
    retargets: [],
  })
  const copiedTotalityScope = onlyNewCut(
    before,
    backward.diagram,
    reviewedHypotheses,
  )
  const copiedTotalityBody = exactOne(
    directCuts(backward.diagram, copiedTotalityScope),
    'copied successor-totality body',
  )
  const derivedSuccessor = nodeWithHead(
    backward.diagram,
    copiedTotalityBody,
    reviewedSuccessor,
  )
  backward.record('specialize successor totality at cited zero', {
    rule: 'wireJoin',
    input: {
      kind: 'iota',
      a: extractedZeroValue,
      b: endpointWire(backward.diagram, derivedSuccessor, 'arg', 0),
    },
  })
  const extractedSuccessorValue = endpointWire(
    backward.diagram,
    derivedSuccessor,
    'arg',
    1,
  )
  backward.record('expose successor of cited zero', {
    rule: 'doubleCutElim',
    region: copiedTotalityScope,
  })

  const citedRulePredecessor = endpointWire(
    backward.diagram,
    citedRuleSuccessorPremise,
    'arg',
    0,
  )
  for (const variable of scopedWires(backward.diagram, citedRuleScope)) {
    const target = variable === citedRulePredecessor
      ? extractedZeroValue
      : extractedSuccessorValue
    backward.record('specialize cited successor-closure rule', {
      rule: 'wireJoin',
      input: {
        kind: 'iota',
        a: target,
        b: variable,
      },
    })
  }
  backward.record(
    'discharge cited predecessor Nat premise',
    deiterationStep(
      backward.diagram,
      citedRuleAntecedent,
      citedRuleNatPremise,
    ),
  )
  backward.record(
    'discharge cited successor premise',
    deiterationStep(
      backward.diagram,
      citedRuleAntecedent,
      citedRuleSuccessorPremise,
    ),
  )
  backward.record('expose cited successor Nat result', {
    rule: 'doubleCutElim',
    region: citedRuleAntecedent,
  })
  backward.record('finish cited successor-closure specialization', {
    rule: 'doubleCutElim',
    region: citedRuleScope,
  })
  if (
    backward.diagram.nodes[extractedZeroNat] === undefined
    || backward.diagram.nodes[citedRuleNatResult] === undefined
  ) {
    throw new Error('cited Nat evidence disappeared')
  }

  const conclusionNodes = directNodes(
    backward.diagram,
    reviewedConclusion!,
  )
  const conclusionZero = nodeWithHead(
    backward.diagram,
    reviewedConclusion!,
    reviewedZero,
  )
  const conclusionSuccessor = nodeWithHead(
    backward.diagram,
    reviewedConclusion!,
    reviewedSuccessor,
  )
  const conclusionNat = exactOne(
    conclusionNodes.filter((node) =>
      backward.diagram.nodes[node]!.kind === 'ref'),
    'one-is-Nat conclusion Nat',
  )
  backward.record('identify reviewed zero witness with cited zero', {
    rule: 'wireJoin',
    input: {
      kind: 'iota',
      a: extractedZeroValue,
      b: endpointWire(backward.diagram, conclusionZero, 'arg', 0),
    },
  })
  backward.record('identify reviewed successor witness with cited result', {
    rule: 'wireJoin',
    input: {
      kind: 'iota',
      a: extractedSuccessorValue,
      b: endpointWire(backward.diagram, conclusionSuccessor, 'arg', 1),
    },
  })
  if (backward.diagram.nodes[conclusionNat] === undefined) {
    throw new Error('reviewed one-is-Nat conclusion disappeared')
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
  for (const variable of scopedWires(backward.diagram, zeroUnique!)) {
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
  backward.record('collapse successor-totality input to zero anchor', {
    rule: 'wireJoin',
    input: {
      kind: 'iota',
      a: existingZeroWire,
      b: endpointWire(backward.diagram, totalSuccessor, 'arg', 0),
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
  const functionalSuccessorInput = endpointWire(
    backward.diagram,
    functionalSuccessorNodes[0]!,
    'arg',
    0,
  )
  for (const variable of scopedWires(
    backward.diagram,
    successorFunctional!,
  )) {
    const target = variable === functionalSuccessorInput
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
  const baseConsequent = exactOne(
    directCuts(backward.diagram, baseAntecedent),
    'addition-base consequent',
  )
  const baseZero = nodeWithHead(
    backward.diagram,
    baseAntecedent,
    reviewedZero,
  )
  const basePlus = nodeWithHead(
    backward.diagram,
    baseConsequent,
    reviewedPlus,
  )
  for (const variable of scopedWires(backward.diagram, additionBase!)) {
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
  for (const variable of scopedWires(backward.diagram, additionStep!)) {
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

  const functionalAdditionBody = exactOne(
    directCuts(backward.diagram, additionFunctional!),
    'functional-addition body',
  )
  const functionalAdditionAntecedent = exactOne(
    directCuts(backward.diagram, functionalAdditionBody),
    'functional-addition antecedent',
  )
  const functionalAdditionPremises = directNodes(
    backward.diagram,
    functionalAdditionAntecedent,
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
  for (const node of functionalAdditionPremises) {
    backward.record(
      'discharge collapsed functional-addition premise',
      deiterationStep(backward.diagram, functionalAdditionAntecedent, node),
    )
  }
  backward.record('remove discharged functional-addition implication', {
    rule: 'doubleCutElim',
    region: functionalAdditionAntecedent,
  })
  backward.record('remove discharged functional-addition quantifier', {
    rule: 'doubleCutElim',
    region: additionFunctional!,
  })
  void basePlus
  void stepPlusResult

  return {
    name: 'oneIsNat',
    lhs,
    rhs,
    actions: forward.actions,
    backActions: backward.actions,
  }
}

export function buildOneTheorem(
  relations: Theory['relations'],
  prefix: readonly Theorem[],
  statements: ArithmeticStatements,
): readonly Theorem[] {
  const context = verifyTheory({ relations, theorems: prefix })
  const one = oneIsNat(statements, context)
  registerTheorem(context, one)
  return Object.freeze([one])
}
