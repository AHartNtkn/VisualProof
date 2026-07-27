import type { Theory } from '../kernel/proof/context'
import { buildArithmeticBase } from './arithmetic-base'
import {
  buildArithmeticAssociativityTheorems,
} from './arithmetic-assoc'
import { buildCommutativityTheorems } from './arithmetic-comm'
import { buildNaturalBaseTheorems } from './arithmetic-naturals'
import { buildOneTheorem } from './arithmetic-one'
import { buildRightUnitTheorem } from './arithmetic-right'
import { buildSuccessorShiftTheorem } from './arithmetic-shift'
import { buildLogicalTheoremPrefix } from './logic'
import { natRelation } from './naturals'
import { buildArithmeticStatements } from './statements'

export { natRelation } from './naturals'

export function buildFregeTheory(): Theory {
  const relations: Theory['relations'] = [
    ['nat', natRelation()],
  ]
  const statements = buildArithmeticStatements()
  const logical = buildLogicalTheoremPrefix(relations)
  const base = buildArithmeticBase(relations, logical, statements)
  const naturals = buildNaturalBaseTheorems(
    relations,
    [...logical, ...base],
    statements,
  )
  const one = buildOneTheorem(
    relations,
    [...logical, ...base, ...naturals],
    statements,
  )
  const right = buildRightUnitTheorem(
    relations,
    [...logical, ...base, ...naturals, ...one],
    statements,
  )
  const associativity = buildArithmeticAssociativityTheorems(
    relations,
    [...logical, ...base, ...naturals, ...one, ...right],
    statements,
  )
  const shift = buildSuccessorShiftTheorem(
    relations,
    [
      ...logical,
      ...base,
      ...naturals,
      ...one,
      ...right,
      ...associativity,
    ],
    statements,
  )
  const commutativity = buildCommutativityTheorems(
    relations,
    [
      ...logical,
      ...base,
      ...naturals,
      ...one,
      ...right,
      ...associativity,
      ...shift,
    ],
    statements,
  )
  return {
    relations,
    theorems: [
      ...logical,
      ...base,
      ...naturals,
      ...one,
      ...right,
      ...associativity,
      ...shift,
      ...commutativity,
    ],
  }
}
