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

export type PrimitiveRelations = {
  readonly zero: WireId
  readonly successor: WireId
  readonly plus: WireId
}

export type ArithmeticStatementName =
  | 'plusLeftUnit'
  | 'zeroIsNat'
  | 'succNat'
  | 'oneIsNat'
  | 'rightIdentityCarrierInductive'
  | 'plusRightUnit'
  | 'associativityCarrierBase'
  | 'associativityCarrierHereditary'
  | 'plusAssoc'
  | 'successorShiftCarrierInductive'
  | 'succShiftS'
  | 'commutativityCarrierInductive'
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

export function drawStandingHypotheses(
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

export function closedStatement(
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

type UnaryCarrierDrawer = (
  graph: GraphConstruction,
  region: RegionId,
  formal: WireId,
  primitives: PrimitiveRelations,
  captures: readonly WireId[],
) => GraphConstruction

function drawAdditionTotality(
  initial: GraphConstruction,
  region: RegionId,
  formal: WireId,
  plus: WireId,
): GraphConstruction {
  const quantified = quantifierScope(initial, region, 'forall', [IOTA])
  const right = quantified.value.variables[0]!
  const output = declareWire(
    quantified.graph,
    quantified.value.body,
    IOTA,
  )
  return atom(
    output.graph,
    quantified.value.body,
    plus,
    [formal, right, output.value],
  ).graph
}

function drawRightIdentityCarrier(
  initial: GraphConstruction,
  region: RegionId,
  formal: WireId,
  primitives: PrimitiveRelations,
): GraphConstruction {
  const quantified = quantifierScope(initial, region, 'forall', [IOTA])
  const zeroValue = quantified.value.variables[0]!
  const claim = implication(quantified.graph, quantified.value.body)
  let graph = claim.graph
  graph = atom(
    graph,
    claim.value.antecedent,
    primitives.zero,
    [zeroValue],
  ).graph
  return atom(
    graph,
    claim.value.consequent,
    primitives.plus,
    [formal, zeroValue, formal],
  ).graph
}

function drawAssociativityCarrier(
  initial: GraphConstruction,
  region: RegionId,
  formal: WireId,
  primitives: PrimitiveRelations,
): GraphConstruction {
  let graph = drawAdditionTotality(
    initial,
    region,
    formal,
    primitives.plus,
  )
  const quantified = quantifierScope(
    graph,
    region,
    'forall',
    [IOTA, IOTA, IOTA, IOTA],
  )
  const [right, third, firstSum, innerSum] =
    quantified.value.variables
  const claim = implication(quantified.graph, quantified.value.body)
  graph = claim.graph
  graph = atom(
    graph,
    claim.value.antecedent,
    primitives.plus,
    [formal, right!, firstSum!],
  ).graph
  graph = atom(
    graph,
    claim.value.antecedent,
    primitives.plus,
    [right!, third!, innerSum!],
  ).graph
  const output = declareWire(graph, claim.value.consequent, IOTA)
  graph = output.graph
  graph = atom(
    graph,
    claim.value.consequent,
    primitives.plus,
    [firstSum!, third!, output.value],
  ).graph
  return atom(
    graph,
    claim.value.consequent,
    primitives.plus,
    [formal, innerSum!, output.value],
  ).graph
}

function drawSuccessorShiftCarrier(
  initial: GraphConstruction,
  region: RegionId,
  formal: WireId,
  primitives: PrimitiveRelations,
): GraphConstruction {
  let graph = drawAdditionTotality(
    initial,
    region,
    formal,
    primitives.plus,
  )
  const quantified = quantifierScope(
    graph,
    region,
    'forall',
    [IOTA, IOTA, IOTA, IOTA],
  )
  const [right, rightSuccessor, output, outputSuccessor] =
    quantified.value.variables
  const claim = implication(quantified.graph, quantified.value.body)
  graph = atom(
    claim.graph,
    claim.value.antecedent,
    primitives.successor,
    [right!, rightSuccessor!],
  ).graph
  graph = atom(
    graph,
    claim.value.antecedent,
    primitives.plus,
    [formal, right!, output!],
  ).graph
  graph = atom(
    graph,
    claim.value.antecedent,
    primitives.successor,
    [output!, outputSuccessor!],
  ).graph
  return atom(
    graph,
    claim.value.consequent,
    primitives.plus,
    [formal, rightSuccessor!, outputSuccessor!],
  ).graph
}

function drawCommutativityCarrier(
  initial: GraphConstruction,
  region: RegionId,
  formal: WireId,
  primitives: PrimitiveRelations,
  captures: readonly WireId[],
): GraphConstruction {
  const fixedRight = captures[0]
  if (fixedRight === undefined || captures.length !== 1) {
    throw new Error('commutativity carrier requires one fixed right addend')
  }
  let graph = drawAdditionTotality(
    initial,
    region,
    formal,
    primitives.plus,
  )
  const quantified = quantifierScope(graph, region, 'forall', [IOTA])
  const output = quantified.value.variables[0]!
  const claim = implication(quantified.graph, quantified.value.body)
  graph = atom(
    claim.graph,
    claim.value.antecedent,
    primitives.plus,
    [formal, fixedRight, output],
  ).graph
  return atom(
    graph,
    claim.value.consequent,
    primitives.plus,
    [fixedRight, formal, output],
  ).graph
}

function drawCarrierInductivity(
  initial: GraphConstruction,
  region: RegionId,
  primitives: PrimitiveRelations,
  drawCarrier: UnaryCarrierDrawer,
  captures: readonly WireId[] = [],
): GraphConstruction {
  const base = quantifierScope(initial, region, 'forall', [IOTA])
  const zeroValue = base.value.variables[0]!
  const baseClaim = implication(base.graph, base.value.body)
  let graph = baseClaim.graph
  graph = atom(
    graph,
    baseClaim.value.antecedent,
    primitives.zero,
    [zeroValue],
  ).graph
  graph = drawCarrier(
    graph,
    baseClaim.value.consequent,
    zeroValue,
    primitives,
    captures,
  )

  const closure = quantifierScope(
    graph,
    region,
    'forall',
    [IOTA, IOTA],
  )
  const [predecessor, successorValue] = closure.value.variables
  const closureClaim = implication(closure.graph, closure.value.body)
  graph = closureClaim.graph
  graph = drawCarrier(
    graph,
    closureClaim.value.antecedent,
    predecessor!,
    primitives,
    captures,
  )
  graph = atom(
    graph,
    closureClaim.value.antecedent,
    primitives.successor,
    [predecessor!, successorValue!],
  ).graph
  return drawCarrier(
    graph,
    closureClaim.value.consequent,
    successorValue!,
    primitives,
    captures,
  )
}

function drawCarrierBase(
  initial: GraphConstruction,
  region: RegionId,
  primitives: PrimitiveRelations,
  drawCarrier: UnaryCarrierDrawer,
  captures: readonly WireId[] = [],
): GraphConstruction {
  const quantified = quantifierScope(initial, region, 'forall', [IOTA])
  const zeroValue = quantified.value.variables[0]!
  const claim = implication(quantified.graph, quantified.value.body)
  let graph = atom(
    claim.graph,
    claim.value.antecedent,
    primitives.zero,
    [zeroValue],
  ).graph
  return drawCarrier(
    graph,
    claim.value.consequent,
    zeroValue,
    primitives,
    captures,
  )
}

function drawCarrierHeredity(
  initial: GraphConstruction,
  region: RegionId,
  primitives: PrimitiveRelations,
  drawCarrier: UnaryCarrierDrawer,
  captures: readonly WireId[] = [],
): GraphConstruction {
  const closure = quantifierScope(
    initial,
    region,
    'forall',
    [IOTA, IOTA],
  )
  const [predecessor, successorValue] = closure.value.variables
  const closureClaim = implication(closure.graph, closure.value.body)
  let graph = drawCarrier(
    closureClaim.graph,
    closureClaim.value.antecedent,
    predecessor!,
    primitives,
    captures,
  )
  graph = atom(
    graph,
    closureClaim.value.antecedent,
    primitives.successor,
    [predecessor!, successorValue!],
  ).graph
  return drawCarrier(
    graph,
    closureClaim.value.consequent,
    successorValue!,
    primitives,
    captures,
  )
}

function rightIdentityCarrierInductiveStatement(): DiagramWithBoundary {
  return closedStatement((initial, region, primitives) =>
    drawCarrierInductivity(
      initial,
      region,
      primitives,
      drawRightIdentityCarrier,
    ))
}

function associativityCarrierHereditaryStatement(): DiagramWithBoundary {
  return closedStatement((initial, region, primitives) =>
    drawCarrierHeredity(
      initial,
      region,
      primitives,
      drawAssociativityCarrier,
    ))
}

function associativityCarrierBaseStatement(): DiagramWithBoundary {
  return closedStatement((initial, region, primitives) =>
    drawCarrierBase(
      initial,
      region,
      primitives,
      drawAssociativityCarrier,
    ))
}

function successorShiftCarrierInductiveStatement(): DiagramWithBoundary {
  return closedStatement((initial, region, primitives) =>
    drawCarrierInductivity(
      initial,
      region,
      primitives,
      drawSuccessorShiftCarrier,
    ))
}

function commutativityCarrierInductiveStatement(): DiagramWithBoundary {
  return closedStatement((initial, region, primitives) => {
    const quantified = quantifierScope(initial, region, 'forall', [IOTA])
    const fixedRight = quantified.value.variables[0]!
    const claim = implication(quantified.graph, quantified.value.body)
    const graph = drawNat(
      claim.graph,
      claim.value.antecedent,
      primitives,
      fixedRight,
    )
    return drawCarrierInductivity(
      graph,
      claim.value.consequent,
      primitives,
      drawCommutativityCarrier,
      [fixedRight],
    )
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
    rightIdentityCarrierInductive:
      rightIdentityCarrierInductiveStatement(),
    plusRightUnit: plusRightUnitStatement(),
    associativityCarrierBase:
      associativityCarrierBaseStatement(),
    associativityCarrierHereditary:
      associativityCarrierHereditaryStatement(),
    plusAssoc: plusAssociativityStatement(),
    successorShiftCarrierInductive:
      successorShiftCarrierInductiveStatement(),
    succShiftS: successorShiftStatement(),
    commutativityCarrierInductive:
      commutativityCarrierInductiveStatement(),
    plusComm: plusCommutativityStatement(),
  })
}
