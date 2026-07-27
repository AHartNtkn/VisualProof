import type { Theory } from '../kernel/proof/context'
import { buildLogicalTheoremPrefix } from './logic'
import { natRelation } from './naturals'

export { natRelation } from './naturals'

export function buildFregeTheory(): Theory {
  const relations: Theory['relations'] = [
    ['nat', natRelation()],
  ]
  return {
    relations,
    theorems: buildLogicalTheoremPrefix(relations),
  }
}
