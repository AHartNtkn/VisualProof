import { application, free, lambda, type Term } from '../../term/term'
import { RuleError } from '../error'

/** Injective embeddings of two numeric free-slot interfaces into one carrier. */
export type SlotCorrespondence = {
  readonly commonArity: number
  readonly left: readonly number[]
  readonly right: readonly number[]
}

export function validateSlotCorrespondenceCarrier(
  correspondence: SlotCorrespondence,
): void {
  if (
    !Number.isSafeInteger(correspondence.commonArity)
    || correspondence.commonArity < 0
  ) {
    throw new RuleError(
      'slot correspondence commonArity must be a non-negative safe integer',
    )
  }
  const covered = new Set<number>()
  for (const side of ['left', 'right'] as const) {
    const seen = new Set<number>()
    for (const [slot, column] of correspondence[side].entries()) {
      if (
        !Number.isSafeInteger(column)
        || column < 0
        || column >= correspondence.commonArity
      ) {
        throw new RuleError(
          `slot correspondence ${side} slot ${slot} column must be a safe integer `
          + `in range 0..<${correspondence.commonArity}`,
        )
      }
      if (seen.has(column)) {
        throw new RuleError(
          `slot correspondence must be injective on the ${side}; `
          + `column ${column} is repeated`,
        )
      }
      seen.add(column)
      covered.add(column)
    }
  }
  if (covered.size !== correspondence.commonArity) {
    let first = 0
    while (covered.has(first)) first++
    throw new RuleError(
      `slot correspondence common column ${first} is uncovered`,
    )
  }
}

export function validateSlotCorrespondence(
  correspondence: SlotCorrespondence,
  leftArity: number,
  rightArity: number,
): void {
  validateSlotCorrespondenceCarrier(correspondence)
  if (correspondence.left.length !== leftArity) {
    throw new RuleError(
      `slot correspondence left side must have arity ${leftArity}, `
      + `got ${correspondence.left.length}`,
    )
  }
  if (correspondence.right.length !== rightArity) {
    throw new RuleError(
      `slot correspondence right side must have arity ${rightArity}, `
      + `got ${correspondence.right.length}`,
    )
  }
}

/** Rename one term's native slots into the correspondence carrier. */
export function mapTermToCommonCarrier(
  term: Term,
  mapping: readonly number[],
): Term {
  switch (term.kind) {
    case 'bound':
      return term
    case 'free': {
      const column = mapping[term.slot]
      if (column === undefined) {
        throw new RuleError(
          `term free slot ${term.slot} is outside correspondence side arity ${mapping.length}`,
        )
      }
      return free(column)
    }
    case 'lambda':
      return lambda(mapTermToCommonCarrier(term.body, mapping))
    case 'application':
      return application(
        mapTermToCommonCarrier(term.fn, mapping),
        mapTermToCommonCarrier(term.argument, mapping),
      )
  }
}
