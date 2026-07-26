import type { Theory } from '../kernel/proof/context'
import {
  associativityInductionReification,
  commutativityInductionReification,
  rightIdentityInductionReification,
  successorShiftInductionReification,
  truthReification,
} from './reification'
import { buildLogicalTheoremPrefix } from './logic'
import { natRelation } from './naturals'

export { natRelation } from './naturals'

export function buildFregeTheory(): Theory {
  const relations: Theory['relations'] = [
    ['truthReification', truthReification()],
    ['rightIdentityInductionReification', rightIdentityInductionReification()],
    ['associativityInductionReification', associativityInductionReification()],
    ['successorShiftInductionReification', successorShiftInductionReification()],
    ['commutativityInductionReification', commutativityInductionReification()],
    ['nat', natRelation()],
  ]
  return {
    relations,
    theorems: buildLogicalTheoremPrefix(relations),
  }
}
