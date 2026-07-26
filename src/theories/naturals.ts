import { IOTA, relSig } from '../kernel/diagram/sig'
import type { DiagramWithBoundary } from '../kernel/diagram/boundary'
import {
  atom,
  declareWire,
  emptyGraph,
  finishDiagramWithBoundary,
  implication,
  quantifierScope,
} from './graph'

const UNARY = relSig([IOTA])
const BINARY = relSig([IOTA, IOTA])

export function natRelation(): DiagramWithBoundary {
  let graph = emptyGraph()
  const zero = declareWire(graph, graph.root, UNARY)
  graph = zero.graph
  const successor = declareWire(graph, graph.root, BINARY)
  graph = successor.graph
  const candidate = declareWire(graph, graph.root, IOTA)
  graph = candidate.graph

  const everyProperty = quantifierScope(
    graph,
    graph.root,
    'forall',
    [UNARY],
  )
  graph = everyProperty.graph
  const property = everyProperty.value.variables[0]!
  const hereditary = implication(graph, everyProperty.value.body)
  graph = hereditary.graph

  const containsZero = quantifierScope(
    graph,
    hereditary.value.antecedent,
    'forall',
    [IOTA],
  )
  graph = containsZero.graph
  const zeroValue = containsZero.value.variables[0]!
  const containsZeroClaim = implication(
    graph,
    containsZero.value.body,
  )
  graph = containsZeroClaim.graph
  graph = atom(
    graph,
    containsZeroClaim.value.antecedent,
    zero.value,
    [zeroValue],
  ).graph
  graph = atom(
    graph,
    containsZeroClaim.value.consequent,
    property,
    [zeroValue],
  ).graph

  const closedUnderSuccessor = quantifierScope(
    graph,
    hereditary.value.antecedent,
    'forall',
    [IOTA, IOTA],
  )
  graph = closedUnderSuccessor.graph
  const [predecessor, successorValue] =
    closedUnderSuccessor.value.variables
  const closureClaim = implication(
    graph,
    closedUnderSuccessor.value.body,
  )
  graph = closureClaim.graph
  graph = atom(
    graph,
    closureClaim.value.antecedent,
    property,
    [predecessor!],
  ).graph
  graph = atom(
    graph,
    closureClaim.value.antecedent,
    successor.value,
    [predecessor!, successorValue!],
  ).graph
  graph = atom(
    graph,
    closureClaim.value.consequent,
    property,
    [successorValue!],
  ).graph

  graph = atom(
    graph,
    hereditary.value.consequent,
    property,
    [candidate.value],
  ).graph
  return finishDiagramWithBoundary(
    graph,
    [zero.value, successor.value, candidate.value],
  )
}
