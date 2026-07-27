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

export type PrimitiveName = 'zero' | 'successor' | 'plus'

export type HypothesisName =
  | 'zeroExists'
  | 'zeroUnique'
  | 'successorTotal'
  | 'successorSingleValued'
  | 'plusBase'
  | 'plusStep'
  | 'plusSingleValued'

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

export type ArithmeticContract = {
  readonly primitives: readonly PrimitiveName[]
  readonly hypotheses: readonly HypothesisName[]
}

export const ARITHMETIC_CONTRACTS: Readonly<
  Record<ArithmeticStatementName, ArithmeticContract>
> = {
  plusLeftUnit: {
    primitives: ['zero', 'plus'],
    hypotheses: ['plusBase', 'plusSingleValued'],
  },
  zeroIsNat: {
    primitives: ['zero', 'successor'],
    hypotheses: ['zeroExists'],
  },
  succNat: { primitives: ['zero', 'successor'], hypotheses: [] },
  oneIsNat: {
    primitives: ['zero', 'successor'],
    hypotheses: ['zeroExists', 'successorTotal'],
  },
  rightIdentityCarrierInductive: {
    primitives: ['zero', 'successor', 'plus'],
    hypotheses: ['zeroUnique', 'plusBase', 'plusStep'],
  },
  plusRightUnit: {
    primitives: ['zero', 'successor', 'plus'],
    hypotheses: ['zeroUnique', 'plusBase', 'plusStep', 'plusSingleValued'],
  },
  associativityCarrierBase: {
    primitives: ['zero', 'plus'],
    hypotheses: ['plusBase', 'plusSingleValued'],
  },
  associativityCarrierHereditary: {
    primitives: ['successor', 'plus'],
    hypotheses: ['successorTotal', 'plusStep', 'plusSingleValued'],
  },
  plusAssoc: {
    primitives: ['zero', 'successor', 'plus'],
    hypotheses: ['successorTotal', 'plusBase', 'plusStep', 'plusSingleValued'],
  },
  successorShiftCarrierInductive: {
    primitives: ['zero', 'successor', 'plus'],
    hypotheses: [
      'successorTotal',
      'successorSingleValued',
      'plusBase',
      'plusStep',
      'plusSingleValued',
    ],
  },
  succShiftS: {
    primitives: ['zero', 'successor', 'plus'],
    hypotheses: [
      'successorTotal',
      'successorSingleValued',
      'plusBase',
      'plusStep',
      'plusSingleValued',
    ],
  },
  commutativityCarrierInductive: {
    primitives: ['zero', 'successor', 'plus'],
    hypotheses: [
      'zeroUnique',
      'successorTotal',
      'successorSingleValued',
      'plusBase',
      'plusStep',
      'plusSingleValued',
    ],
  },
  plusComm: {
    primitives: ['zero', 'successor', 'plus'],
    hypotheses: [
      'zeroUnique',
      'successorTotal',
      'successorSingleValued',
      'plusBase',
      'plusStep',
      'plusSingleValued',
    ],
  },
}

type PrimitiveEnvironment =
  Readonly<Partial<Record<PrimitiveName, WireId>>>

const PRIMITIVE_SIGNATURES: Readonly<Record<PrimitiveName, typeof UNARY>> = {
  zero: UNARY,
  successor: BINARY,
  plus: TERNARY,
}

function requirePrimitive(
  environment: PrimitiveEnvironment,
  name: PrimitiveName,
): WireId {
  const primitive = environment[name]
  if (primitive === undefined) {
    throw new Error(`arithmetic statement requires primitive '${name}'`)
  }
  return primitive
}

function drawNat(
  graph: GraphConstruction,
  region: RegionId,
  primitives: PrimitiveEnvironment,
  individual: WireId,
): GraphConstruction {
  const zero = requirePrimitive(primitives, 'zero')
  const successor = requirePrimitive(primitives, 'successor')
  return ref(
    graph,
    region,
    'nat',
    [
      zero,
      successor,
      individual,
    ],
  ).graph
}

function drawHypothesis(
  graph: GraphConstruction,
  region: RegionId,
  primitives: PrimitiveEnvironment,
  name: HypothesisName,
): GraphConstruction {
  switch (name) {
    case 'zeroExists': {
      const witness = declareWire(graph, region, IOTA)
      return atom(witness.graph, region, requirePrimitive(primitives, 'zero'), [witness.value]).graph
    }
    case 'zeroUnique': {
      const quantified = quantifierScope(graph, region, 'forall', [IOTA, IOTA])
      const [first, second] = quantified.value.variables
      const claim = implication(quantified.graph, quantified.value.body)
      graph = atom(claim.graph, claim.value.antecedent, requirePrimitive(primitives, 'zero'), [first!]).graph
      graph = atom(graph, claim.value.antecedent, requirePrimitive(primitives, 'zero'), [second!]).graph
      return identity(graph, claim.value.consequent, [first!, second!]).graph
    }
    case 'successorTotal': {
      const quantified = quantifierScope(graph, region, 'forall', [IOTA])
      const output = declareWire(quantified.graph, quantified.value.body, IOTA)
      return atom(output.graph, quantified.value.body, requirePrimitive(primitives, 'successor'), [quantified.value.variables[0]!, output.value]).graph
    }
    case 'successorSingleValued': {
      const quantified = quantifierScope(graph, region, 'forall', [IOTA, IOTA, IOTA])
      const [input, first, second] = quantified.value.variables
      const claim = implication(quantified.graph, quantified.value.body)
      graph = atom(claim.graph, claim.value.antecedent, requirePrimitive(primitives, 'successor'), [input!, first!]).graph
      graph = atom(graph, claim.value.antecedent, requirePrimitive(primitives, 'successor'), [input!, second!]).graph
      return identity(graph, claim.value.consequent, [first!, second!]).graph
    }
    case 'plusBase': {
      const quantified = quantifierScope(graph, region, 'forall', [IOTA, IOTA])
      const [zeroValue, right] = quantified.value.variables
      const claim = implication(quantified.graph, quantified.value.body)
      graph = atom(claim.graph, claim.value.antecedent, requirePrimitive(primitives, 'zero'), [zeroValue!]).graph
      return atom(graph, claim.value.consequent, requirePrimitive(primitives, 'plus'), [zeroValue!, right!, right!]).graph
    }
    case 'plusStep': {
      const quantified = quantifierScope(graph, region, 'forall', [IOTA, IOTA, IOTA, IOTA, IOTA])
      const [left, right, output, leftSuccessor, outputSuccessor] = quantified.value.variables
      const claim = implication(quantified.graph, quantified.value.body)
      graph = atom(claim.graph, claim.value.antecedent, requirePrimitive(primitives, 'plus'), [left!, right!, output!]).graph
      graph = atom(graph, claim.value.antecedent, requirePrimitive(primitives, 'successor'), [left!, leftSuccessor!]).graph
      graph = atom(graph, claim.value.antecedent, requirePrimitive(primitives, 'successor'), [output!, outputSuccessor!]).graph
      return atom(graph, claim.value.consequent, requirePrimitive(primitives, 'plus'), [leftSuccessor!, right!, outputSuccessor!]).graph
    }
    case 'plusSingleValued': {
      const quantified = quantifierScope(graph, region, 'forall', [IOTA, IOTA, IOTA, IOTA])
      const [left, right, first, second] = quantified.value.variables
      const claim = implication(quantified.graph, quantified.value.body)
      graph = atom(claim.graph, claim.value.antecedent, requirePrimitive(primitives, 'plus'), [left!, right!, first!]).graph
      graph = atom(graph, claim.value.antecedent, requirePrimitive(primitives, 'plus'), [left!, right!, second!]).graph
      return identity(graph, claim.value.consequent, [first!, second!]).graph
    }
  }
}

function closedStatement(
  contract: ArithmeticContract,
  drawConclusion: (
    graph: GraphConstruction,
    region: RegionId,
    primitives: PrimitiveEnvironment,
  ) => GraphConstruction,
): DiagramWithBoundary {
  let graph = emptyGraph()
  const quantifiedPrimitives = quantifierScope(
    graph,
    graph.root,
    'forall',
    contract.primitives.map((name) => PRIMITIVE_SIGNATURES[name]),
  )
  graph = quantifiedPrimitives.graph
  const primitives: Partial<Record<PrimitiveName, WireId>> = {}
  contract.primitives.forEach((name, index) => {
    primitives[name] = quantifiedPrimitives.value.variables[index]!
  })
  const theorem = implication(graph, quantifiedPrimitives.value.body)
  graph = theorem.graph
  for (const hypothesis of contract.hypotheses) {
    graph = drawHypothesis(graph, theorem.value.antecedent, primitives, hypothesis)
  }
  graph = drawConclusion(
    graph,
    theorem.value.consequent,
    primitives,
  )
  return finishDiagramWithBoundary(graph, [])
}

function plusLeftUnitStatement(): DiagramWithBoundary {
  return closedStatement(ARITHMETIC_CONTRACTS.plusLeftUnit, (initial, region, primitives) => {
    const zero = requirePrimitive(primitives, 'zero')
    const plus = requirePrimitive(primitives, 'plus')
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
      zero,
      [zeroValue!],
    ).graph
    graph = atom(
      graph,
      claim.value.antecedent,
      plus,
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
  return closedStatement(ARITHMETIC_CONTRACTS.plusRightUnit, (initial, region, primitives) => {
    const zero = requirePrimitive(primitives, 'zero')
    const plus = requirePrimitive(primitives, 'plus')
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
      zero,
      [zeroValue!],
    ).graph
    graph = atom(
      graph,
      claim.value.antecedent,
      plus,
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
  primitives: PrimitiveEnvironment,
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
  primitives: PrimitiveEnvironment,
): GraphConstruction {
  const zero = requirePrimitive(primitives, 'zero')
  const plus = requirePrimitive(primitives, 'plus')
  const quantified = quantifierScope(initial, region, 'forall', [IOTA])
  const zeroValue = quantified.value.variables[0]!
  const claim = implication(quantified.graph, quantified.value.body)
  let graph = claim.graph
  graph = atom(
    graph,
    claim.value.antecedent,
    zero,
    [zeroValue],
  ).graph
  return atom(
    graph,
    claim.value.consequent,
    plus,
    [formal, zeroValue, formal],
  ).graph
}

function drawAssociativityCarrier(
  initial: GraphConstruction,
  region: RegionId,
  formal: WireId,
  primitives: PrimitiveEnvironment,
): GraphConstruction {
  const plus = requirePrimitive(primitives, 'plus')
  let graph = drawAdditionTotality(
    initial,
    region,
    formal,
    plus,
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
    plus,
    [formal, right!, firstSum!],
  ).graph
  graph = atom(
    graph,
    claim.value.antecedent,
    plus,
    [right!, third!, innerSum!],
  ).graph
  const output = declareWire(graph, claim.value.consequent, IOTA)
  graph = output.graph
  graph = atom(
    graph,
    claim.value.consequent,
    plus,
    [firstSum!, third!, output.value],
  ).graph
  return atom(
    graph,
    claim.value.consequent,
    plus,
    [formal, innerSum!, output.value],
  ).graph
}

function drawSuccessorShiftCarrier(
  initial: GraphConstruction,
  region: RegionId,
  formal: WireId,
  primitives: PrimitiveEnvironment,
): GraphConstruction {
  const successor = requirePrimitive(primitives, 'successor')
  const plus = requirePrimitive(primitives, 'plus')
  let graph = drawAdditionTotality(
    initial,
    region,
    formal,
    plus,
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
    successor,
    [right!, rightSuccessor!],
  ).graph
  graph = atom(
    graph,
    claim.value.antecedent,
    plus,
    [formal, right!, output!],
  ).graph
  graph = atom(
    graph,
    claim.value.antecedent,
    successor,
    [output!, outputSuccessor!],
  ).graph
  return atom(
    graph,
    claim.value.consequent,
    plus,
    [formal, rightSuccessor!, outputSuccessor!],
  ).graph
}

function drawCommutativityCarrier(
  initial: GraphConstruction,
  region: RegionId,
  formal: WireId,
  primitives: PrimitiveEnvironment,
  captures: readonly WireId[],
): GraphConstruction {
  const fixedRight = captures[0]
  if (fixedRight === undefined || captures.length !== 1) {
    throw new Error('commutativity carrier requires one fixed right addend')
  }
  const plus = requirePrimitive(primitives, 'plus')
  let graph = drawAdditionTotality(
    initial,
    region,
    formal,
    plus,
  )
  const quantified = quantifierScope(graph, region, 'forall', [IOTA])
  const output = quantified.value.variables[0]!
  const claim = implication(quantified.graph, quantified.value.body)
  graph = atom(
    claim.graph,
    claim.value.antecedent,
    plus,
    [formal, fixedRight, output],
  ).graph
  return atom(
    graph,
    claim.value.consequent,
    plus,
    [fixedRight, formal, output],
  ).graph
}

function drawCarrierInductivity(
  initial: GraphConstruction,
  region: RegionId,
  primitives: PrimitiveEnvironment,
  drawCarrier: UnaryCarrierDrawer,
  captures: readonly WireId[] = [],
): GraphConstruction {
  const zero = requirePrimitive(primitives, 'zero')
  const successor = requirePrimitive(primitives, 'successor')
  const base = quantifierScope(initial, region, 'forall', [IOTA])
  const zeroValue = base.value.variables[0]!
  const baseClaim = implication(base.graph, base.value.body)
  let graph = baseClaim.graph
  graph = atom(
    graph,
    baseClaim.value.antecedent,
    zero,
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
    successor,
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
  primitives: PrimitiveEnvironment,
  drawCarrier: UnaryCarrierDrawer,
  captures: readonly WireId[] = [],
): GraphConstruction {
  const zero = requirePrimitive(primitives, 'zero')
  const quantified = quantifierScope(initial, region, 'forall', [IOTA])
  const zeroValue = quantified.value.variables[0]!
  const claim = implication(quantified.graph, quantified.value.body)
  let graph = atom(
    claim.graph,
    claim.value.antecedent,
    zero,
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
  primitives: PrimitiveEnvironment,
  drawCarrier: UnaryCarrierDrawer,
  captures: readonly WireId[] = [],
): GraphConstruction {
  const successor = requirePrimitive(primitives, 'successor')
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
    successor,
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
  return closedStatement(ARITHMETIC_CONTRACTS.rightIdentityCarrierInductive, (initial, region, primitives) =>
    drawCarrierInductivity(
      initial,
      region,
      primitives,
      drawRightIdentityCarrier,
    ))
}

function associativityCarrierHereditaryStatement(): DiagramWithBoundary {
  return closedStatement(ARITHMETIC_CONTRACTS.associativityCarrierHereditary, (initial, region, primitives) =>
    drawCarrierHeredity(
      initial,
      region,
      primitives,
      drawAssociativityCarrier,
    ))
}

function associativityCarrierBaseStatement(): DiagramWithBoundary {
  return closedStatement(ARITHMETIC_CONTRACTS.associativityCarrierBase, (initial, region, primitives) =>
    drawCarrierBase(
      initial,
      region,
      primitives,
      drawAssociativityCarrier,
    ))
}

function successorShiftCarrierInductiveStatement(): DiagramWithBoundary {
  return closedStatement(ARITHMETIC_CONTRACTS.successorShiftCarrierInductive, (initial, region, primitives) =>
    drawCarrierInductivity(
      initial,
      region,
      primitives,
      drawSuccessorShiftCarrier,
    ))
}

function commutativityCarrierInductiveStatement(): DiagramWithBoundary {
  return closedStatement(ARITHMETIC_CONTRACTS.commutativityCarrierInductive, (initial, region, primitives) => {
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
  return closedStatement(ARITHMETIC_CONTRACTS.plusAssoc, (initial, region, primitives) => {
    const plus = requirePrimitive(primitives, 'plus')
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
      plus,
      [left!, right!, firstSum!],
    ).graph
    graph = atom(
      graph,
      claim.value.antecedent,
      plus,
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
      plus,
      [right!, third!, innerSum.value],
    ).graph
    return atom(
      graph,
      claim.value.consequent,
      plus,
      [left!, innerSum.value, output!],
    ).graph
  })
}

function zeroIsNatStatement(): DiagramWithBoundary {
  return closedStatement(ARITHMETIC_CONTRACTS.zeroIsNat, (initial, region, primitives) => {
    const zero = requirePrimitive(primitives, 'zero')
    const zeroValue = declareWire(initial, region, IOTA)
    let graph = zeroValue.graph
    graph = atom(
      graph,
      region,
      zero,
      [zeroValue.value],
    ).graph
    return drawNat(graph, region, primitives, zeroValue.value)
  })
}

function successorNatStatement(): DiagramWithBoundary {
  return closedStatement(ARITHMETIC_CONTRACTS.succNat, (initial, region, primitives) => {
    const successor = requirePrimitive(primitives, 'successor')
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
      successor,
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
  return closedStatement(ARITHMETIC_CONTRACTS.oneIsNat, (initial, region, primitives) => {
    const zero = requirePrimitive(primitives, 'zero')
    const successor = requirePrimitive(primitives, 'successor')
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
      zero,
      [zeroValue.value],
    ).graph
    graph = atom(
      graph,
      region,
      successor,
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
  return closedStatement(ARITHMETIC_CONTRACTS.succShiftS, (initial, region, primitives) => {
    const successor = requirePrimitive(primitives, 'successor')
    const plus = requirePrimitive(primitives, 'plus')
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
      successor,
      [right!, rightSuccessor!],
    ).graph
    graph = atom(
      graph,
      claim.value.antecedent,
      plus,
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
      plus,
      [left!, right!, predecessorSum.value],
    ).graph
    return atom(
      graph,
      claim.value.consequent,
      successor,
      [predecessorSum.value, output!],
    ).graph
  })
}

function plusCommutativityStatement(): DiagramWithBoundary {
  return closedStatement(ARITHMETIC_CONTRACTS.plusComm, (initial, region, primitives) => {
    const plus = requirePrimitive(primitives, 'plus')
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
      plus,
      [left!, right!, output!],
    ).graph
    return atom(
      graph,
      claim.value.consequent,
      plus,
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
