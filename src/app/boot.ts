import type { DiagramWithBoundary } from '../kernel/diagram/boundary'
import type { ProofContext } from '../kernel/proof/context'
import { assertProofContext, verifyTheory } from '../kernel/proof/context'
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
  readonly relations: readonly (readonly [string, DiagramWithBoundary])[]
}

/**
 * Merge verified theories into one proof context. Theorem and relation names
 * must be disjoint. Every conflict refuses loudly — a silent shadow would
 * change what a citation means.
 */
export function mergeTheories(loaded: readonly { theory: Theory; ctx: ProofContext }[]): BootContext {
  const relations: Array<readonly [string, DiagramWithBoundary]> = []
  const theorems: Theorem[] = []
  const theoremNames = new Set<string>()
  const relationNames = new Set<string>()
  for (const { ctx } of loaded) {
    assertProofContext(ctx)
    for (const name of ctx.theorems.keys()) {
      if (theoremNames.has(name)) throw new Error(`theory merge conflict: duplicate theorem '${name}'`)
      theoremNames.add(name)
    }
    for (const name of ctx.relations.keys()) {
      if (relationNames.has(name)) throw new Error(`theory merge conflict: duplicate relation '${name}'`)
      relationNames.add(name)
    }
  }
  for (const name of relationNames) {
    if (theoremNames.has(name)) throw new Error(`theory merge conflict: '${name}' names both a relation and theorem`)
  }
  for (const { ctx } of loaded) {
    assertProofContext(ctx)
    for (const [name, rel] of ctx.relations) {
      relations.push([name, rel])
    }
    for (const theorem of ctx.theorems.values()) {
      theorems.push(theorem)
    }
  }
  return { ctx: verifyTheory({ relations, theorems }), relations }
}
