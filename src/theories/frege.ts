import type { DiagramWithBoundary } from '../kernel/diagram/boundary'
import type { Theory } from '../kernel/proof/context'
import {
  emptyGraph,
  finishDiagramWithBoundary,
} from './graph'
import {
  associativityInductionReification,
  commutativityInductionReification,
  rightIdentityInductionReification,
  successorShiftInductionReification,
  truthReification,
} from './reification'
import { buildLogicalTheoremPrefix } from './logic'

export function natRelation(): DiagramWithBoundary {
  const graph = emptyGraph()
  return finishDiagramWithBoundary(graph, [])
}

export function buildFregeTheory(): Theory {
  const relations: Theory['relations'] = [
    ['truthReification', truthReification()],
    ['rightIdentityInductionReification', rightIdentityInductionReification()],
    ['associativityInductionReification', associativityInductionReification()],
    ['successorShiftInductionReification', successorShiftInductionReification()],
    ['commutativityInductionReification', commutativityInductionReification()],
  ]
  return {
    relations,
    theorems: buildLogicalTheoremPrefix(relations),
  }
}
