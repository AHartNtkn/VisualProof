import type {
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
  BINARY,
  TERNARY,
  UNARY,
  deiterationStep,
  directCuts,
  directNodes,
  endpointWire,
  exactOne,
  introducedContentSelection,
  nodeWithHead,
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

function zeroIsNat(
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

  forward.record('iterate zero evidence into the conclusion', {
    rule: 'iteration',
    sel: {
      region: hypotheses,
      regions: [],
      nodes: [zeroAnchor],
      wires: [],
    },
    target: conclusion,
    retargets: [],
  })

  before = forward.diagram
  forward.record('open Nat property universal scope', {
    rule: 'doubleCutIntro',
    sel: {
      region: conclusion,
      regions: [],
      nodes: [],
      wires: [],
    },
  })
  const propertyScope = onlyNewCut(before, forward.diagram, conclusion)
  const propertyBody = exactOne(
    directCuts(forward.diagram, propertyScope),
    'Nat property body',
  )
  before = forward.diagram
  forward.record('introduce arbitrary hereditary property', {
    rule: 'vacuousIntro',
    scope: propertyScope,
    sig: UNARY,
  })
  const property = onlyNewWire(before, forward.diagram, propertyScope)

  before = forward.diagram
  forward.record('open Nat hereditary implication', {
    rule: 'doubleCutIntro',
    sel: {
      region: propertyBody,
      regions: [],
      nodes: [],
      wires: [],
    },
  })
  const hereditary = onlyNewCut(before, forward.diagram, propertyBody)
  const inherited = exactOne(
    directCuts(forward.diagram, hereditary),
    'Nat hereditary result',
  )

  before = forward.diagram
  forward.record('insert hereditary base result', {
    rule: 'atomSpawn',
    region: hereditary,
    wire: property,
  })
  const propertyAtZero = onlyNewNode(before, forward.diagram, hereditary)
  forward.record('attach hereditary base result to zero', {
    rule: 'wireJoin',
    input: {
      kind: 'iota',
      a: zeroValue,
      b: endpointWire(forward.diagram, propertyAtZero, 'arg', 0),
    },
  })

  before = forward.diagram
  forward.record('insert hereditary closure anchor', {
    rule: 'atomSpawn',
    region: hereditary,
    wire: property,
  })
  const propertyAtSuccessor = onlyNewNode(
    before,
    forward.diagram,
    hereditary,
  )
  forward.record('attach hereditary closure anchor to successor', {
    rule: 'wireJoin',
    input: {
      kind: 'iota',
      a: successorValue,
      b: endpointWire(
      forward.diagram,
      propertyAtSuccessor,
      'arg',
      0,
    ),
    },
  })
  forward.record('iterate hereditary base result to candidate', {
    rule: 'iteration',
    sel: {
      region: hereditary,
      regions: [],
      nodes: [propertyAtZero],
      wires: [],
    },
    target: inherited,
    retargets: [],
  })

  const rhs = statements.zeroIsNat
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

  const conclusionNodes = directNodes(
    backward.diagram,
    reviewedConclusion!,
  )
  const conclusionZero = exactOne(
    conclusionNodes.filter((node) =>
      backward.diagram.nodes[node]!.kind === 'atom'),
    'zero conclusion evidence',
  )
  const conclusionNat = exactOne(
    conclusionNodes.filter((node) =>
      backward.diagram.nodes[node]!.kind === 'ref'),
    'zero conclusion Nat reference',
  )
  const conclusionZeroWire = endpointWire(
    backward.diagram,
    conclusionZero,
    'arg',
    0,
  )
  backward.record('identify conclusion zero witness with existing zero', {
    rule: 'wireJoin',
    input: {
      kind: 'iota',
      a: existingZeroWire,
      b: conclusionZeroWire,
    },
  })
  before = backward.diagram
  backward.record('unfold parameterized Nat at zero', {
    rule: 'unfold',
    nodeId: conclusionNat,
  })
  const unfoldedPropertyScope = onlyNewCut(
    before,
    backward.diagram,
    reviewedConclusion!,
  )
  const unfoldedPropertyBody = exactOne(
    directCuts(backward.diagram, unfoldedPropertyScope),
    'unfolded Nat property body',
  )
  const unfoldedHereditary = exactOne(
    directCuts(backward.diagram, unfoldedPropertyBody),
    'unfolded Nat hereditary antecedent',
  )
  const propertyWire = exactOne(
    scopedWires(backward.diagram, unfoldedPropertyScope),
    'unfolded Nat property wire',
  )
  const conditionScopes = directCuts(
    backward.diagram,
    unfoldedHereditary,
  )
  if (conditionScopes.length !== 3) {
    throw new Error(
      `expected inherited result plus base and closure, found ${conditionScopes.length}`,
    )
  }
  const [unfoldedInherited, baseCondition, closureCondition] =
    conditionScopes
  void unfoldedInherited

  before = backward.diagram
  backward.record('copy Nat base condition for the zero witness', {
    rule: 'iteration',
    sel: {
      region: unfoldedHereditary,
      regions: [baseCondition!],
      nodes: [],
      wires: [],
    },
    target: unfoldedHereditary,
    retargets: [],
  })
  const copiedBaseScope = onlyNewCut(
    before,
    backward.diagram,
    unfoldedHereditary,
  )
  const copiedBaseBody = exactOne(
    directCuts(backward.diagram, copiedBaseScope),
    'copied Nat base body',
  )
  const copiedBaseAntecedent = exactOne(
    directCuts(backward.diagram, copiedBaseBody),
    'copied Nat base antecedent',
  )
  const copiedBaseConsequent = exactOne(
    directCuts(backward.diagram, copiedBaseAntecedent),
    'copied Nat base consequent',
  )
  const copiedBaseZero = nodeWithHead(
    backward.diagram,
    copiedBaseAntecedent,
    reviewedZero,
  )
  const copiedBaseProperty = nodeWithHead(
    backward.diagram,
    copiedBaseConsequent,
    propertyWire,
  )
  backward.record('specialize copied Nat base at zero', {
    rule: 'wireJoin',
    input: {
      kind: 'iota',
      a: existingZeroWire,
      b: endpointWire(backward.diagram, copiedBaseZero, 'arg', 0),
    },
  })
  backward.record(
    'discharge copied Nat zero premise',
    deiterationStep(
      backward.diagram,
      copiedBaseAntecedent,
      copiedBaseZero,
    ),
  )
  backward.record('expose copied Nat base result', {
    rule: 'doubleCutElim',
    region: copiedBaseAntecedent,
  })
  backward.record('finish copied Nat base specialization', {
    rule: 'doubleCutElim',
    region: copiedBaseScope,
  })

  const originalBaseBody = exactOne(
    directCuts(backward.diagram, baseCondition!),
    'original Nat base body',
  )
  const originalBaseAntecedent = exactOne(
    directCuts(backward.diagram, originalBaseBody),
    'original Nat base antecedent',
  )
  const originalBaseConsequent = exactOne(
    directCuts(backward.diagram, originalBaseAntecedent),
    'original Nat base consequent',
  )
  const originalBaseZero = nodeWithHead(
    backward.diagram,
    originalBaseAntecedent,
    reviewedZero,
  )
  const originalBaseProperty = nodeWithHead(
    backward.diagram,
    originalBaseConsequent,
    propertyWire,
  )
  backward.record('specialize original Nat base at zero', {
    rule: 'wireJoin',
    input: {
      kind: 'iota',
      a: existingZeroWire,
      b: endpointWire(backward.diagram, originalBaseZero, 'arg', 0),
    },
  })
  backward.record(
    'discharge original Nat zero premise',
    deiterationStep(
      backward.diagram,
      originalBaseAntecedent,
      originalBaseZero,
    ),
  )
  backward.record('expose original Nat base result', {
    rule: 'doubleCutElim',
    region: originalBaseAntecedent,
  })
  backward.record('finish original Nat base specialization', {
    rule: 'doubleCutElim',
    region: baseCondition!,
  })
  backward.record(
    'remove duplicate Nat base result',
    deiterationStep(
      backward.diagram,
      unfoldedHereditary,
      originalBaseProperty,
    ),
  )
  if (backward.diagram.nodes[copiedBaseProperty] === undefined) {
    throw new Error('copied Nat base result disappeared')
  }

  const closureBody = exactOne(
    directCuts(backward.diagram, closureCondition!),
    'Nat closure body',
  )
  const closureAntecedent = exactOne(
    directCuts(backward.diagram, closureBody),
    'Nat closure antecedent',
  )
  const closureConsequent = exactOne(
    directCuts(backward.diagram, closureAntecedent),
    'Nat closure consequent',
  )
  const closurePremises = directNodes(backward.diagram, closureAntecedent)
  const closurePropertyPremise = nodeWithHead(
    backward.diagram,
    closureAntecedent,
    propertyWire,
  )
  const closureSuccessorPremise = nodeWithHead(
    backward.diagram,
    closureAntecedent,
    reviewedSuccessor,
  )
  const closurePropertyResult = nodeWithHead(
    backward.diagram,
    closureConsequent,
    propertyWire,
  )
  const closureInput = endpointWire(
    backward.diagram,
    closureSuccessorPremise,
    'arg',
    0,
  )
  for (const variable of scopedWires(backward.diagram, closureCondition!)) {
    const target = variable === closureInput
      ? existingZeroWire
      : successorAnchorOutput
    backward.record('specialize Nat closure variable to successor anchor', {
      rule: 'wireJoin',
      input: {
        kind: 'iota',
        a: target,
        b: variable,
      },
    })
  }
  backward.record(
    'discharge Nat closure property premise',
    deiterationStep(
      backward.diagram,
      closureAntecedent,
      closurePropertyPremise,
    ),
  )
  backward.record(
    'discharge Nat closure successor premise',
    deiterationStep(
      backward.diagram,
      closureAntecedent,
      closureSuccessorPremise,
    ),
  )
  backward.record('expose Nat closure anchor', {
    rule: 'doubleCutElim',
    region: closureAntecedent,
  })
  backward.record('finish Nat closure specialization', {
    rule: 'doubleCutElim',
    region: closureCondition!,
  })
  if (
    closurePremises.length !== 2
    || backward.diagram.nodes[closurePropertyResult] === undefined
  ) {
    throw new Error('Nat closure specialization lost its result')
  }

  void basePlus
  void stepPlusResult
  return {
    name: 'zeroIsNat',
    lhs,
    rhs,
    actions: forward.actions,
    backActions: backward.actions,
  }
}

function succNat(
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

  forward.record('open successor-closure universal scope', {
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
    'successor-closure universal body',
  )
  const claimVariables: WireId[] = []
  for (const label of ['predecessor', 'successor']) {
    before = forward.diagram
    forward.record(`introduce successor-closure ${label}`, {
      rule: 'vacuousIntro',
      scope: claimScope,
      sig: IOTA,
    })
    claimVariables.push(onlyNewWire(before, forward.diagram, claimScope))
  }
  const [predecessor, successorResult] = claimVariables as [
    WireId,
    WireId,
  ]

  before = forward.diagram
  forward.record('open successor-closure implication', {
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
    'successor-closure consequent',
  )

  before = forward.diagram
  forward.record('introduce temporary predecessor-Nat proposition', {
    rule: 'vacuousIntro',
    scope: claimAntecedent,
    sig: relSig([]),
  })
  const temporaryNat = onlyNewWire(
    before,
    forward.diagram,
    claimAntecedent,
  )
  before = forward.diagram
  forward.record('insert temporary predecessor-Nat assertion', {
    rule: 'atomSpawn',
    region: claimAntecedent,
    wire: temporaryNat,
  })
  onlyNewNode(before, forward.diagram, claimAntecedent)
  before = forward.diagram
  forward.record('ground predecessor Nat on the supplied primitives', {
    rule: 'wireJoin',
    input: {
      kind: 'relation',
      wire: temporaryNat,
      content: natRelation(),
      parameters: [zero, successor, predecessor],
    },
  })
  const predecessorNatMaterial = introducedContentSelection(
    before,
    forward.diagram,
    claimAntecedent,
  )
  before = forward.diagram
  forward.record('fold the grounded predecessor Nat premise', {
    rule: 'fold',
    occurrence: predecessorNatMaterial,
    args: [zero, successor, predecessor],
    defId: 'nat',
  })
  const predecessorNat = onlyNewNode(
    before,
    forward.diagram,
    claimAntecedent,
  )

  before = forward.diagram
  forward.record('insert successor-closure premise', {
    rule: 'atomSpawn',
    region: claimAntecedent,
    wire: successor,
  })
  const successorPremise = onlyNewNode(
    before,
    forward.diagram,
    claimAntecedent,
  )
  forward.record('attach successor-closure predecessor', {
    rule: 'wireJoin',
    input: {
      kind: 'iota',
      a: predecessor,
      b: endpointWire(forward.diagram, successorPremise, 'arg', 0),
    },
  })
  forward.record('attach successor-closure successor', {
    rule: 'wireJoin',
    input: {
      kind: 'iota',
      a: successorResult,
      b: endpointWire(forward.diagram, successorPremise, 'arg', 1),
    },
  })

  before = forward.diagram
  forward.record('iterate predecessor Nat into the conclusion', {
    rule: 'iteration',
    sel: {
      region: claimAntecedent,
      regions: [],
      nodes: [predecessorNat],
      wires: [],
    },
    target: claimConsequent,
    retargets: [],
  })
  const copiedNat = onlyNewNode(
    before,
    forward.diagram,
    claimConsequent,
  )

  before = forward.diagram
  forward.record('unfold the copied predecessor Nat', {
    rule: 'unfold',
    nodeId: copiedNat,
  })
  const propertyScope = onlyNewCut(
    before,
    forward.diagram,
    claimConsequent,
  )
  const propertyBody = exactOne(
    directCuts(forward.diagram, propertyScope),
    'unfolded Nat property body',
  )
  const hereditary = exactOne(
    directCuts(forward.diagram, propertyBody),
    'unfolded Nat hereditary antecedent',
  )
  const property = exactOne(
    scopedWires(forward.diagram, propertyScope),
    'unfolded Nat property wire',
  )
  const hereditaryChildren = directCuts(forward.diagram, hereditary)
  if (hereditaryChildren.length !== 3) {
    throw new Error(
      `expected inherited result plus two conditions, found ${hereditaryChildren.length}`,
    )
  }
  const [inherited, , closureCondition] = hereditaryChildren
  const predecessorProperty = nodeWithHead(
    forward.diagram,
    inherited!,
    property,
  )

  before = forward.diagram
  forward.record('copy hereditary closure into the Nat result', {
    rule: 'iteration',
    sel: {
      region: hereditary,
      regions: [closureCondition!],
      nodes: [],
      wires: [],
    },
    target: inherited!,
    retargets: [],
  })
  const copiedClosureScope = onlyNewCut(
    before,
    forward.diagram,
    inherited!,
  )
  const copiedClosureBody = exactOne(
    directCuts(forward.diagram, copiedClosureScope),
    'copied closure body',
  )
  const copiedClosureAntecedent = exactOne(
    directCuts(forward.diagram, copiedClosureBody),
    'copied closure antecedent',
  )
  const copiedClosureConsequent = exactOne(
    directCuts(forward.diagram, copiedClosureAntecedent),
    'copied closure consequent',
  )
  const copiedPropertyPremise = nodeWithHead(
    forward.diagram,
    copiedClosureAntecedent,
    property,
  )
  const copiedSuccessorPremise = nodeWithHead(
    forward.diagram,
    copiedClosureAntecedent,
    successor,
  )
  const successorProperty = nodeWithHead(
    forward.diagram,
    copiedClosureConsequent,
    property,
  )
  const copiedClosureInput = endpointWire(
    forward.diagram,
    copiedSuccessorPremise,
    'arg',
    0,
  )
  for (const variable of scopedWires(
    forward.diagram,
    copiedClosureScope,
  )) {
    const target = variable === copiedClosureInput
      ? predecessor
      : successorResult
    forward.record('specialize copied hereditary closure', {
      rule: 'wireJoin',
      input: {
        kind: 'iota',
        a: target,
        b: variable,
      },
    })
  }
  forward.record(
    'discharge copied predecessor property premise',
    deiterationStep(
      forward.diagram,
      copiedClosureAntecedent,
      copiedPropertyPremise,
    ),
  )
  forward.record(
    'discharge copied successor premise',
    deiterationStep(
      forward.diagram,
      copiedClosureAntecedent,
      copiedSuccessorPremise,
    ),
  )
  forward.record('expose copied successor property', {
    rule: 'doubleCutElim',
    region: copiedClosureAntecedent,
  })
  forward.record('finish copied hereditary closure', {
    rule: 'doubleCutElim',
    region: copiedClosureScope,
  })
  forward.record('erase the predecessor property result', {
    rule: 'erasure',
    sel: {
      region: inherited!,
      regions: [],
      nodes: [predecessorProperty],
      wires: [],
    },
  })
  if (forward.diagram.nodes[successorProperty] === undefined) {
    throw new Error('successor property result disappeared')
  }
  forward.record('fold the successor Nat result', {
    rule: 'fold',
    occurrence: {
      region: claimConsequent,
      regions: [propertyScope],
      nodes: [],
      wires: [],
    },
    args: [zero, successor, successorResult],
    defId: 'nat',
  })

  const rhs = statements.succNat
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
  void reviewedConclusion
  void basePlus
  void stepPlusResult

  return {
    name: 'succNat',
    lhs,
    rhs,
    actions: forward.actions,
    backActions: backward.actions,
  }
}

export function buildNaturalBaseTheorems(
  relations: Theory['relations'],
  prefix: readonly Theorem[],
  statements: ArithmeticStatements,
): readonly Theorem[] {
  let context = verifyTheory({ relations, theorems: prefix })
  const zero = zeroIsNat(statements, context)
  context = registerTheorem(context, zero)
  const successor = succNat(statements, context)
  context = registerTheorem(context, successor)
  void context
  return Object.freeze([zero, successor])
}
