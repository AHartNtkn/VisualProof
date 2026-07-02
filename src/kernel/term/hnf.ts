import type { Term } from './term'
import type { PathSeg, ReductionStep } from './reduce'
import { applyStepAt } from './reduce'

export type SpineHead =
  | { readonly kind: 'bound'; readonly index: number }
  | { readonly kind: 'free'; readonly name: string }
  | { readonly kind: 'redex' }

export type HeadSpine = {
  readonly binders: number
  readonly head: SpineHead
  readonly args: readonly Term[]
}

/**
 * Structural spine analysis, no reduction. Strips the binder prefix (every
 * leading lam), then unwinds the application spine; the head is the
 * leftmost-innermost application target under the binder prefix. A lam in
 * head position is necessarily applied (an unapplied lam would have been part
 * of the binder prefix), so its kind is 'redex'. The free head carries the
 * port name only because terms key free ports by name; it is plumbing, not
 * semantics.
 */
export function headSpine(t: Term): HeadSpine {
  let binders = 0
  let cur = t
  while (cur.kind === 'lam') { binders++; cur = cur.body }
  const args: Term[] = []
  while (cur.kind === 'app') { args.push(cur.arg); cur = cur.fn }
  args.reverse()
  switch (cur.kind) {
    case 'bvar': return { binders, head: { kind: 'bound', index: cur.index }, args }
    case 'port': return { binders, head: { kind: 'free', name: cur.name }, args }
    case 'lam': return { binders, head: { kind: 'redex' }, args }
  }
}

/**
 * Path to the head redex of a spine whose head kind is 'redex': descend the
 * binder prefix, then down the application spine to the innermost app — the
 * one whose fn is the lam.
 */
function headRedexStep(spine: HeadSpine): ReductionStep {
  const path: PathSeg[] = []
  for (let i = 0; i < spine.binders; i++) path.push('body')
  for (let i = 0; i < spine.args.length - 1; i++) path.push('fn')
  return { kind: 'beta', path }
}

function reduceHead(
  t: Term,
  fuel: number,
  enterBinders: boolean,
  fnName: string,
): { term: Term; steps: readonly ReductionStep[] } {
  if (!Number.isInteger(fuel) || fuel <= 0) {
    throw new Error(`fuel must be a positive integer, got ${fuel}`)
  }
  const steps: ReductionStep[] = []
  let cur = t
  let remaining = fuel
  for (;;) {
    if (!enterBinders && cur.kind === 'lam') return { term: cur, steps }
    const spine = headSpine(cur)
    if (spine.head.kind !== 'redex') return { term: cur, steps }
    if (remaining === 0) {
      throw new Error(`${fnName} exhausted its fuel of ${fuel} steps without reaching a rigid head; the head reduction appears divergent`)
    }
    const step = headRedexStep(spine)
    cur = applyStepAt(cur, step)
    steps.push(step)
    remaining--
  }
}

/**
 * Head normalization: repeated HEAD beta steps only (the spine redex,
 * descending under the binder prefix) until the head is bound/free,
 * recording each step for certificate consumption; arguments are never
 * reduced. Throws on fuel exhaustion.
 */
export function headNormalize(t: Term, fuel: number): { term: Term; steps: readonly ReductionStep[] } {
  return reduceHead(t, fuel, true, 'headNormalize')
}

/**
 * Weak head normalization: like headNormalize, except it never descends under
 * a binder — a term with a non-empty binder prefix is already in weak head
 * normal form.
 */
export function weakHeadNormalize(t: Term, fuel: number): { term: Term; steps: readonly ReductionStep[] } {
  return reduceHead(t, fuel, false, 'weakHeadNormalize')
}
