import { IOTA, relSig } from '../kernel/diagram/sig'
import type { DiagramWithBoundary } from '../kernel/diagram/boundary'
import type { RegionId, WireId } from '../kernel/diagram/diagram'
import {
  atom,
  biconditional,
  declareWire,
  emptyGraph,
  finishDiagramWithBoundary,
  identity,
  implication,
  quantifierScope,
  type GraphConstruction,
} from './graph'

const UNARY = relSig([IOTA])
const BINARY = relSig([IOTA, IOTA])
const TERNARY = relSig([IOTA, IOTA, IOTA])

function drawRightIdentityAssertion(
  initial: GraphConstruction,
  region: RegionId,
  inductionVariable: WireId,
  zero: WireId,
  plus: WireId,
): GraphConstruction {
  const quantified = quantifierScope(initial, region, 'forall', [IOTA, IOTA])
  const [zeroValue, output] = quantified.value.variables
  const claim = implication(quantified.graph, quantified.value.body)
  let graph = claim.graph
  graph = atom(graph, claim.value.antecedent, zero, [zeroValue!]).graph
  graph = atom(
    graph,
    claim.value.antecedent,
    plus,
    [inductionVariable, zeroValue!, output!],
  ).graph
  return identity(
    graph,
    claim.value.consequent,
    [output!, inductionVariable],
  ).graph
}

function drawAssociativityAssertion(
  initial: GraphConstruction,
  region: RegionId,
  inductionVariable: WireId,
  plus: WireId,
): GraphConstruction {
  const quantified = quantifierScope(
    initial,
    region,
    'forall',
    [IOTA, IOTA, IOTA, IOTA, IOTA],
  )
  const [right, third, firstSum, output, innerSum] = quantified.value.variables
  const claim = implication(quantified.graph, quantified.value.body)
  let graph = claim.graph
  graph = atom(
    graph,
    claim.value.antecedent,
    plus,
    [inductionVariable, right!, firstSum!],
  ).graph
  graph = atom(
    graph,
    claim.value.antecedent,
    plus,
    [firstSum!, third!, output!],
  ).graph
  graph = atom(
    graph,
    claim.value.antecedent,
    plus,
    [right!, third!, innerSum!],
  ).graph
  return atom(
    graph,
    claim.value.consequent,
    plus,
    [inductionVariable, innerSum!, output!],
  ).graph
}

function drawSuccessorShiftAssertion(
  initial: GraphConstruction,
  region: RegionId,
  inductionVariable: WireId,
  successor: WireId,
  plus: WireId,
): GraphConstruction {
  const quantified = quantifierScope(
    initial,
    region,
    'forall',
    [IOTA, IOTA, IOTA, IOTA],
  )
  const [right, rightSuccessor, output, outputSuccessor] =
    quantified.value.variables
  const claim = implication(quantified.graph, quantified.value.body)
  let graph = claim.graph
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
    [inductionVariable, right!, output!],
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
    [inductionVariable, rightSuccessor!, outputSuccessor!],
  ).graph
}

function drawCommutativityAssertion(
  initial: GraphConstruction,
  region: RegionId,
  inductionVariable: WireId,
  plus: WireId,
): GraphConstruction {
  const quantified = quantifierScope(initial, region, 'forall', [IOTA, IOTA])
  const [right, output] = quantified.value.variables
  const claim = implication(quantified.graph, quantified.value.body)
  let graph = claim.graph
  graph = atom(
    graph,
    claim.value.antecedent,
    plus,
    [inductionVariable, right!, output!],
  ).graph
  return atom(
    graph,
    claim.value.consequent,
    plus,
    [right!, inductionVariable, output!],
  ).graph
}

export function truthReification(): DiagramWithBoundary {
  let graph = emptyGraph()
  const witness = declareWire(graph, graph.root, relSig([]))
  graph = witness.graph
  const iff = biconditional(graph, graph.root)
  graph = iff.graph
  graph = atom(graph, iff.value.forward.antecedent, witness.value, []).graph
  graph = atom(graph, iff.value.reverse.consequent, witness.value, []).graph
  return finishDiagramWithBoundary(graph, [witness.value])
}

export function rightIdentityInductionReification(): DiagramWithBoundary {
  let graph = emptyGraph()
  const witness = declareWire(graph, graph.root, UNARY)
  graph = witness.graph
  const zero = declareWire(graph, graph.root, UNARY)
  graph = zero.graph
  const plus = declareWire(graph, graph.root, TERNARY)
  graph = plus.graph
  const quantified = quantifierScope(graph, graph.root, 'forall', [IOTA])
  graph = quantified.graph
  const inductionVariable = quantified.value.variables[0]!
  const iff = biconditional(graph, quantified.value.body)
  graph = iff.graph
  graph = atom(
    graph,
    iff.value.forward.antecedent,
    witness.value,
    [inductionVariable],
  ).graph
  graph = drawRightIdentityAssertion(
    graph,
    iff.value.forward.consequent,
    inductionVariable,
    zero.value,
    plus.value,
  )
  graph = drawRightIdentityAssertion(
    graph,
    iff.value.reverse.antecedent,
    inductionVariable,
    zero.value,
    plus.value,
  )
  graph = atom(
    graph,
    iff.value.reverse.consequent,
    witness.value,
    [inductionVariable],
  ).graph
  return finishDiagramWithBoundary(
    graph,
    [witness.value, zero.value, plus.value],
  )
}

export function associativityInductionReification(): DiagramWithBoundary {
  let graph = emptyGraph()
  const witness = declareWire(graph, graph.root, UNARY)
  graph = witness.graph
  const plus = declareWire(graph, graph.root, TERNARY)
  graph = plus.graph
  const quantified = quantifierScope(graph, graph.root, 'forall', [IOTA])
  graph = quantified.graph
  const inductionVariable = quantified.value.variables[0]!
  const iff = biconditional(graph, quantified.value.body)
  graph = iff.graph
  graph = atom(
    graph,
    iff.value.forward.antecedent,
    witness.value,
    [inductionVariable],
  ).graph
  graph = drawAssociativityAssertion(
    graph,
    iff.value.forward.consequent,
    inductionVariable,
    plus.value,
  )
  graph = drawAssociativityAssertion(
    graph,
    iff.value.reverse.antecedent,
    inductionVariable,
    plus.value,
  )
  graph = atom(
    graph,
    iff.value.reverse.consequent,
    witness.value,
    [inductionVariable],
  ).graph
  return finishDiagramWithBoundary(graph, [witness.value, plus.value])
}

export function successorShiftInductionReification(): DiagramWithBoundary {
  let graph = emptyGraph()
  const witness = declareWire(graph, graph.root, UNARY)
  graph = witness.graph
  const successor = declareWire(graph, graph.root, BINARY)
  graph = successor.graph
  const plus = declareWire(graph, graph.root, TERNARY)
  graph = plus.graph
  const quantified = quantifierScope(graph, graph.root, 'forall', [IOTA])
  graph = quantified.graph
  const inductionVariable = quantified.value.variables[0]!
  const iff = biconditional(graph, quantified.value.body)
  graph = iff.graph
  graph = atom(
    graph,
    iff.value.forward.antecedent,
    witness.value,
    [inductionVariable],
  ).graph
  graph = drawSuccessorShiftAssertion(
    graph,
    iff.value.forward.consequent,
    inductionVariable,
    successor.value,
    plus.value,
  )
  graph = drawSuccessorShiftAssertion(
    graph,
    iff.value.reverse.antecedent,
    inductionVariable,
    successor.value,
    plus.value,
  )
  graph = atom(
    graph,
    iff.value.reverse.consequent,
    witness.value,
    [inductionVariable],
  ).graph
  return finishDiagramWithBoundary(
    graph,
    [witness.value, successor.value, plus.value],
  )
}

export function commutativityInductionReification(): DiagramWithBoundary {
  let graph = emptyGraph()
  const witness = declareWire(graph, graph.root, UNARY)
  graph = witness.graph
  const plus = declareWire(graph, graph.root, TERNARY)
  graph = plus.graph
  const quantified = quantifierScope(graph, graph.root, 'forall', [IOTA])
  graph = quantified.graph
  const inductionVariable = quantified.value.variables[0]!
  const iff = biconditional(graph, quantified.value.body)
  graph = iff.graph
  graph = atom(
    graph,
    iff.value.forward.antecedent,
    witness.value,
    [inductionVariable],
  ).graph
  graph = drawCommutativityAssertion(
    graph,
    iff.value.forward.consequent,
    inductionVariable,
    plus.value,
  )
  graph = drawCommutativityAssertion(
    graph,
    iff.value.reverse.antecedent,
    inductionVariable,
    plus.value,
  )
  graph = atom(
    graph,
    iff.value.reverse.consequent,
    witness.value,
    [inductionVariable],
  ).graph
  return finishDiagramWithBoundary(graph, [witness.value, plus.value])
}
