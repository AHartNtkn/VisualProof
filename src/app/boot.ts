import type { Term } from '../kernel/term/term'
import { serializeTerm } from '../kernel/term/serialize'
import type { DiagramWithBoundary } from '../kernel/diagram/boundary'
import type { ProofContext } from '../kernel/proof/step'
import type { Theorem } from '../kernel/proof/theorem'
import type { Theory } from '../kernel/proof/store'
import { loadTheory, theoryToJson } from '../kernel/proof/store'
import { buildFregeTheory } from '../theories/frege'
import { buildLambdaTheory } from '../theories/lambda'

export type BootContext = {
  readonly ctx: ProofContext
  readonly relations: Readonly<Record<string, DiagramWithBoundary>>
  readonly constNames: ReadonlySet<string>
}

/**
 * Merge verified theories into one proof context. Definitions may overlap
 * only with serializeTerm-identical bodies; theorem and relation names must
 * be disjoint. Every conflict refuses loudly — a silent shadow would change
 * what a citation means.
 */
export function mergeTheories(loaded: readonly { theory: Theory; ctx: ProofContext }[]): BootContext {
  const definitions: Record<string, Term> = {}
  const theorems = new Map<string, Theorem>()
  const relations: Record<string, DiagramWithBoundary> = {}
  for (const { theory, ctx } of loaded) {
    for (const [id, body] of Object.entries(theory.definitions)) {
      const existing = definitions[id]
      if (existing !== undefined && serializeTerm(existing) !== serializeTerm(body)) {
        throw new Error(`theory merge conflict: definition '${id}' has different bodies in the two bundles`)
      }
      definitions[id] = body
    }
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
    ctx: { definitions, theorems },
    relations,
    constNames: new Set(Object.keys(definitions)),
  }
}

/** The app's boot path: both bundled theories through the verifying JSON road. */
export function bootBundledContext(): BootContext {
  return mergeTheories([
    loadTheory(theoryToJson(buildFregeTheory())),
    loadTheory(theoryToJson(buildLambdaTheory())),
  ])
}
