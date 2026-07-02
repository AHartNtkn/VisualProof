import type { DiagramWithBoundary } from '../kernel/diagram/boundary'
import type { ProofContext } from '../kernel/proof/step'
import type { Theory } from '../kernel/proof/store'

/**
 * The live context as a saveable Theory. Map insertion order IS dependency
 * order (boot loads verified theories in order; adopt appends), which is
 * exactly what verifyTheory requires of the theorems array.
 */
export function sessionTheory(
  ctx: ProofContext,
  extras: { readonly relations: Readonly<Record<string, DiagramWithBoundary>> },
): Theory {
  return {
    relations: extras.relations,
    theorems: [...ctx.theorems.values()],
  }
}
