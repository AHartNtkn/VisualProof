import type { DiagramWithBoundary } from '../kernel/diagram/boundary'
import type { RegionId, WireId } from '../kernel/diagram/diagram'
import { IOTA, relSig } from '../kernel/diagram/sig'
import {
  atom,
  declareWire,
  emptyGraph,
  finishDiagramWithBoundary,
  identity,
  implication,
  quantifierScope,
  ref,
  type GraphConstruction,
} from './graph'

const UNARY = relSig([IOTA])
const BINARY = relSig([IOTA, IOTA])
const TERNARY = relSig([IOTA, IOTA, IOTA])

type PrimitiveRelations = {
  readonly zero: WireId
  readonly successor: WireId
  readonly plus: WireId
}

export type ArithmeticStatementName =
  | 'plusLeftUnit'
  | 'zeroIsNat'
  | 'succNat'
  | 'oneIsNat'
  | 'plusRightUnit'
  | 'plusAssoc'
  | 'succShiftS'
  | 'plusComm'

export type ArithmeticStatements = Readonly<
  Record<ArithmeticStatementName, DiagramWithBoundary>
>

function drawNat(
  graph: GraphConstruction,
  region: RegionId,
  primitives: PrimitiveRelations,
  individual: WireId,
): GraphConstruction {
  return ref(
    graph,
    region,
    'nat',
    [primitives.zero, primitives.successor, individual],
  ).graph
}

function drawStandingHypotheses(
  initial: GraphConstruction,
  region: RegionId,
  primitives: PrimitiveRelations,
): GraphConstruction {
  let graph = initial

  const existingZero = declareWire(graph, region, IOTA)
  graph = existingZero.graph
  graph = atom(
    graph,
    region,
    primitives.zero,
    [existingZero.value],
  ).graph

  const uniqueZero = quantifierScope(
    graph,
    region,
    'forall',
    [IOTA, IOTA],
  )
  graph = uniqueZero.graph
  const [firstZero, secondZero] = uniqueZero.value.variables
  const uniqueZeroClaim = implication(graph, uniqueZero.value.body)
  graph = uniqueZeroClaim.graph
  graph = atom(
    graph,
    uniqueZeroClaim.value.antecedent,
    primitives.zero,
    [firstZero!],
  ).graph
  graph = atom(
    graph,
    uniqueZeroClaim.value.antecedent,
    primitives.zero,
    [secondZero!],
  ).graph
  graph = identity(
    graph,
    uniqueZeroClaim.value.consequent,
    [firstZero!, secondZero!],
  ).graph

  const totalSuccessor = quantifierScope(
    graph,
    region,
    'forall',
    [IOTA],
  )
  graph = totalSuccessor.graph
  const predecessor = totalSuccessor.value.variables[0]!
  const successorValue = declareWire(
    graph,
    totalSuccessor.value.body,
    IOTA,
  )
  graph = successorValue.graph
  graph = atom(
    graph,
    totalSuccessor.value.body,
    primitives.successor,
    [predecessor, successorValue.value],
  ).graph

  const functionalSuccessor = quantifierScope(
    graph,
    region,
    'forall',
    [IOTA, IOTA, IOTA],
  )
  graph = functionalSuccessor.graph
  const [input, firstOutput, secondOutput] =
    functionalSuccessor.value.variables
  const functionalSuccessorClaim = implication(
    graph,
    functionalSuccessor.value.body,
  )
  graph = functionalSuccessorClaim.graph
  graph = atom(
    graph,
    functionalSuccessorClaim.value.antecedent,
    primitives.successor,
    [input!, firstOutput!],
  ).graph
  graph = atom(
    graph,
    functionalSuccessorClaim.value.antecedent,
    primitives.successor,
    [input!, secondOutput!],
  ).graph
  graph = identity(
    graph,
    functionalSuccessorClaim.value.consequent,
    [firstOutput!, secondOutput!],
  ).graph

  const additionBase = quantifierScope(
    graph,
    region,
    'forall',
    [IOTA, IOTA],
  )
  graph = additionBase.graph
  const [zeroValue, right] = additionBase.value.variables
  const additionBaseClaim = implication(
    graph,
    additionBase.value.body,
  )
  graph = additionBaseClaim.graph
  graph = atom(
    graph,
    additionBaseClaim.value.antecedent,
    primitives.zero,
    [zeroValue!],
  ).graph
  graph = atom(
    graph,
    additionBaseClaim.value.consequent,
    primitives.plus,
    [zeroValue!, right!, right!],
  ).graph

  const additionStep = quantifierScope(
    graph,
    region,
    'forall',
    [IOTA, IOTA, IOTA, IOTA, IOTA],
  )
  graph = additionStep.graph
  const [left, stepRight, output, leftSuccessor, outputSuccessor] =
    additionStep.value.variables
  const additionStepClaim = implication(
    graph,
    additionStep.value.body,
  )
  graph = additionStepClaim.graph
  graph = atom(
    graph,
    additionStepClaim.value.antecedent,
    primitives.plus,
    [left!, stepRight!, output!],
  ).graph
  graph = atom(
    graph,
    additionStepClaim.value.antecedent,
    primitives.successor,
    [left!, leftSuccessor!],
  ).graph
  graph = atom(
    graph,
    additionStepClaim.value.antecedent,
    primitives.successor,
    [output!, outputSuccessor!],
  ).graph
  graph = atom(
    graph,
    additionStepClaim.value.consequent,
    primitives.plus,
    [leftSuccessor!, stepRight!, outputSuccessor!],
  ).graph

  const functionalAddition = quantifierScope(
    graph,
    region,
    'forall',
    [IOTA, IOTA, IOTA, IOTA],
  )
  graph = functionalAddition.graph
  const [functionLeft, functionRight, firstSum, secondSum] =
    functionalAddition.value.variables
  const functionalAdditionClaim = implication(
    graph,
    functionalAddition.value.body,
  )
  graph = functionalAdditionClaim.graph
  graph = atom(
    graph,
    functionalAdditionClaim.value.antecedent,
    primitives.plus,
    [functionLeft!, functionRight!, firstSum!],
  ).graph
  graph = atom(
    graph,
    functionalAdditionClaim.value.antecedent,
    primitives.plus,
    [functionLeft!, functionRight!, secondSum!],
  ).graph
  graph = identity(
    graph,
    functionalAdditionClaim.value.consequent,
    [firstSum!, secondSum!],
  ).graph

  return graph
}

function closedStatement(
  drawConclusion: (
    graph: GraphConstruction,
    region: RegionId,
    primitives: PrimitiveRelations,
  ) => GraphConstruction,
): DiagramWithBoundary {
  let graph = emptyGraph()
  const quantifiedPrimitives = quantifierScope(
    graph,
    graph.root,
    'forall',
    [UNARY, BINARY, TERNARY],
  )
  graph = quantifiedPrimitives.graph
  const [zero, successor, plus] = quantifiedPrimitives.value.variables
  const primitives: PrimitiveRelations = {
    zero: zero!,
    successor: successor!,
    plus: plus!,
  }
  const theorem = implication(graph, quantifiedPrimitives.value.body)
  graph = theorem.graph
  graph = drawStandingHypotheses(
    graph,
    theorem.value.antecedent,
    primitives,
  )
  graph = drawConclusion(
    graph,
    theorem.value.consequent,
    primitives,
  )
  return finishDiagramWithBoundary(graph, [])
}

function plusLeftUnitStatement(): DiagramWithBoundary {
  return closedStatement((initial, region, primitives) => {
    const quantified = quantifierScope(
      initial,
      region,
      'forall',
      [IOTA, IOTA, IOTA],
    )
    const [zeroValue, addend, output] = quantified.value.variables
    const claim = implication(
      quantified.graph,
      quantified.value.body,
    )
    let graph = claim.graph
    graph = atom(
      graph,
      claim.value.antecedent,
      primitives.zero,
      [zeroValue!],
    ).graph
    graph = atom(
      graph,
      claim.value.antecedent,
      primitives.plus,
      [zeroValue!, addend!, output!],
    ).graph
    return identity(
      graph,
      claim.value.consequent,
      [output!, addend!],
    ).graph
  })
}

function plusRightUnitStatement(): DiagramWithBoundary {
  return closedStatement((initial, region, primitives) => {
    const quantified = quantifierScope(
      initial,
      region,
      'forall',
      [IOTA, IOTA, IOTA],
    )
    const [zeroValue, addend, output] = quantified.value.variables
    const claim = implication(
      quantified.graph,
      quantified.value.body,
    )
    let graph = claim.graph
    graph = drawNat(
      graph,
      claim.value.antecedent,
      primitives,
      addend!,
    )
    graph = atom(
      graph,
      claim.value.antecedent,
      primitives.zero,
      [zeroValue!],
    ).graph
    graph = atom(
      graph,
      claim.value.antecedent,
      primitives.plus,
      [addend!, zeroValue!, output!],
    ).graph
    return identity(
      graph,
      claim.value.consequent,
      [output!, addend!],
    ).graph
  })
}

function plusAssociativityStatement(): DiagramWithBoundary {
  return closedStatement((initial, region, primitives) => {
    const quantified = quantifierScope(
      initial,
      region,
      'forall',
      [IOTA, IOTA, IOTA, IOTA, IOTA],
    )
    const [left, right, third, firstSum, output] =
      quantified.value.variables
    const claim = implication(
      quantified.graph,
      quantified.value.body,
    )
    let graph = claim.graph
    graph = drawNat(
      graph,
      claim.value.antecedent,
      primitives,
      left!,
    )
    graph = atom(
      graph,
      claim.value.antecedent,
      primitives.plus,
      [left!, right!, firstSum!],
    ).graph
    graph = atom(
      graph,
      claim.value.antecedent,
      primitives.plus,
      [firstSum!, third!, output!],
    ).graph
    const innerSum = declareWire(
      graph,
      claim.value.consequent,
      IOTA,
    )
    graph = innerSum.graph
    graph = atom(
      graph,
      claim.value.consequent,
      primitives.plus,
      [right!, third!, innerSum.value],
    ).graph
    return atom(
      graph,
      claim.value.consequent,
      primitives.plus,
      [left!, innerSum.value, output!],
    ).graph
  })
}

function zeroIsNatStatement(): DiagramWithBoundary {
  return closedStatement((initial, region, primitives) => {
    const zeroValue = declareWire(initial, region, IOTA)
    let graph = zeroValue.graph
    graph = atom(
      graph,
      region,
      primitives.zero,
      [zeroValue.value],
    ).graph
    return drawNat(graph, region, primitives, zeroValue.value)
  })
}

function successorNatStatement(): DiagramWithBoundary {
  return closedStatement((initial, region, primitives) => {
    const quantified = quantifierScope(
      initial,
      region,
      'forall',
      [IOTA, IOTA],
    )
    const [predecessor, successorValue] = quantified.value.variables
    const claim = implication(
      quantified.graph,
      quantified.value.body,
    )
    let graph = claim.graph
    graph = drawNat(
      graph,
      claim.value.antecedent,
      primitives,
      predecessor!,
    )
    graph = atom(
      graph,
      claim.value.antecedent,
      primitives.successor,
      [predecessor!, successorValue!],
    ).graph
    return drawNat(
      graph,
      claim.value.consequent,
      primitives,
      successorValue!,
    )
  })
}

function oneIsNatStatement(): DiagramWithBoundary {
  return closedStatement((initial, region, primitives) => {
    const zeroValue = declareWire(initial, region, IOTA)
    const successorValue = declareWire(
      zeroValue.graph,
      region,
      IOTA,
    )
    let graph = successorValue.graph
    graph = atom(
      graph,
      region,
      primitives.zero,
      [zeroValue.value],
    ).graph
    graph = atom(
      graph,
      region,
      primitives.successor,
      [zeroValue.value, successorValue.value],
    ).graph
    return drawNat(
      graph,
      region,
      primitives,
      successorValue.value,
    )
  })
}

function successorShiftStatement(): DiagramWithBoundary {
  return closedStatement((initial, region, primitives) => {
    const quantified = quantifierScope(
      initial,
      region,
      'forall',
      [IOTA, IOTA, IOTA, IOTA],
    )
    const [left, right, rightSuccessor, output] =
      quantified.value.variables
    const claim = implication(
      quantified.graph,
      quantified.value.body,
    )
    let graph = claim.graph
    graph = drawNat(
      graph,
      claim.value.antecedent,
      primitives,
      left!,
    )
    graph = atom(
      graph,
      claim.value.antecedent,
      primitives.successor,
      [right!, rightSuccessor!],
    ).graph
    graph = atom(
      graph,
      claim.value.antecedent,
      primitives.plus,
      [left!, rightSuccessor!, output!],
    ).graph
    const predecessorSum = declareWire(
      graph,
      claim.value.consequent,
      IOTA,
    )
    graph = predecessorSum.graph
    graph = atom(
      graph,
      claim.value.consequent,
      primitives.plus,
      [left!, right!, predecessorSum.value],
    ).graph
    return atom(
      graph,
      claim.value.consequent,
      primitives.successor,
      [predecessorSum.value, output!],
    ).graph
  })
}

function plusCommutativityStatement(): DiagramWithBoundary {
  return closedStatement((initial, region, primitives) => {
    const quantified = quantifierScope(
      initial,
      region,
      'forall',
      [IOTA, IOTA, IOTA],
    )
    const [left, right, output] = quantified.value.variables
    const claim = implication(
      quantified.graph,
      quantified.value.body,
    )
    let graph = claim.graph
    graph = drawNat(
      graph,
      claim.value.antecedent,
      primitives,
      left!,
    )
    graph = drawNat(
      graph,
      claim.value.antecedent,
      primitives,
      right!,
    )
    graph = atom(
      graph,
      claim.value.antecedent,
      primitives.plus,
      [left!, right!, output!],
    ).graph
    return atom(
      graph,
      claim.value.consequent,
      primitives.plus,
      [right!, left!, output!],
    ).graph
  })
}

export function buildArithmeticStatements(): ArithmeticStatements {
  return Object.freeze({
    plusLeftUnit: plusLeftUnitStatement(),
    zeroIsNat: zeroIsNatStatement(),
    succNat: successorNatStatement(),
    oneIsNat: oneIsNatStatement(),
    plusRightUnit: plusRightUnitStatement(),
    plusAssoc: plusAssociativityStatement(),
    succShiftS: successorShiftStatement(),
    plusComm: plusCommutativityStatement(),
  })
}
