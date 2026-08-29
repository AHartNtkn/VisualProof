import type { ReductionStep } from './reduce'
import { applyStepAt } from './reduce'
import type { Term } from './term'

export type SpineHead =
  | { readonly kind: 'bound'; readonly index: number }
  | { readonly kind: 'free'; readonly slot: number }
  | { readonly kind: 'redex' }

export type HeadSpine = {
  readonly binders: number
  readonly head: SpineHead
  readonly args: readonly Term[]
}

export type ReductionTrace = {
  readonly term: Term
  readonly steps: readonly ReductionStep[]
}

export function headSpine(term: Term): HeadSpine {
  let binders = 0
  let current = term
  while (current.kind === 'lambda') {
    binders++
    current = current.body
  }
  const args: Term[] = []
  while (current.kind === 'application') {
    args.push(current.argument)
    current = current.fn
  }
  args.reverse()
  switch (current.kind) {
    case 'bound': return { binders, head: { kind: 'bound', index: current.index }, args }
    case 'free': return { binders, head: { kind: 'free', slot: current.slot }, args }
    case 'lambda': return { binders, head: { kind: 'redex' }, args }
  }
}

function headRedexStep(spine: HeadSpine): ReductionStep {
  const path: ('body' | 'fn')[] = []
  for (let index = 0; index < spine.binders; index++) path.push('body')
  for (let index = 0; index < spine.args.length - 1; index++) path.push('fn')
  return { kind: 'beta', path }
}

function reduceHead(
  term: Term,
  fuel: number,
  enterBinders: boolean,
  functionName: string,
): ReductionTrace {
  if (!Number.isInteger(fuel) || fuel <= 0) {
    throw new Error(`fuel must be a positive integer, got ${fuel}`)
  }
  const steps: ReductionStep[] = []
  let current = term
  let remaining = fuel
  for (;;) {
    if (!enterBinders && current.kind === 'lambda') return { term: current, steps }
    const spine = headSpine(current)
    if (spine.head.kind !== 'redex') return { term: current, steps }
    if (remaining === 0) {
      throw new Error(`${functionName} exhausted its fuel of ${fuel} steps without reaching a rigid head; the head reduction appears divergent`)
    }
    const step = headRedexStep(spine)
    current = applyStepAt(current, step)
    steps.push(step)
    remaining--
  }
}

export function headNormalize(term: Term, fuel: number): ReductionTrace {
  return reduceHead(term, fuel, true, 'headNormalize')
}

export function weakHeadNormalize(term: Term, fuel: number): ReductionTrace {
  return reduceHead(term, fuel, false, 'weakHeadNormalize')
}
