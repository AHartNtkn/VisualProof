import type { DiagramWithBoundary } from '../kernel/diagram/boundary'
import type { ProofContext } from '../kernel/proof/step'
import type { Theorem } from '../kernel/proof/theorem'
import type { Theory } from '../kernel/proof/store'

/**
 * The merged working context. There is NO boot fetch and NO manifest: the app
 * starts with zero knowledge of any theory file. Content enters only when the
 * user opens files/folders through the library, so this type is just the shape
 * `mergeTheories` (and the library's rebuild) produce.
 */
export type BootContext = {
  readonly ctx: ProofContext
  readonly relations: Readonly<Record<string, DiagramWithBoundary>>
}

/**
 * Merge verified theories into one proof context. Theorem and relation names
 * must be disjoint. Every conflict refuses loudly — a silent shadow would
 * change what a citation means.
 */
export function mergeTheories(loaded: readonly { theory: Theory; ctx: ProofContext }[]): BootContext {
  const theorems = new Map<string, Theorem>()
  const relations: Record<string, DiagramWithBoundary> = {}
  for (const { theory, ctx } of loaded) {
    for (const [name, thm] of ctx.theorems) {
      if (theorems.has(name)) throw new Error(`theory merge conflict: duplicate theorem '${name}'`)
      theorems.set(name, thm)
    }
    for (const [name, rel] of Object.entries(theory.relations)) {
      if (relations[name] !== undefined) throw new Error(`theory merge conflict: duplicate relation '${name}'`)
      relations[name] = rel
    }
  }
  return {
    ctx: { theorems, relations: new Map(Object.entries(relations)) },
    relations,
  }
}
