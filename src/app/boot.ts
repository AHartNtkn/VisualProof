import type { Term } from '../kernel/term/term'
import { serializeTerm } from '../kernel/term/serialize'
import type { DiagramWithBoundary } from '../kernel/diagram/boundary'
import type { ProofContext } from '../kernel/proof/step'
import type { Theorem } from '../kernel/proof/theorem'
import type { Theory } from '../kernel/proof/store'
import { loadTheory } from '../kernel/proof/store'

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
    ctx: { definitions, theorems, relations: new Map(Object.entries(relations)) },
    relations,
    constNames: new Set(Object.keys(definitions)),
  }
}

/** Where the shipped theory data lives, relative to the served app root. */
const MANIFEST_URL = 'theories/index.json'
const theoryUrl = (file: string): string => `theories/${file}`

/**
 * The app's boot path: read the shipped theory files as DATA and bring each one
 * into the kernel through loadTheory (parse + verify), then merge. `fetchJson`
 * abstracts the transport — the browser passes a fetch-based reader; tests pass
 * an in-memory reader built from the generators + theoryToJson, exercising the
 * real load path minus HTTP. Every failure (missing manifest, malformed file,
 * unverifiable theory) propagates loudly; there is no empty-context fallback.
 */
export async function fetchBootContext(
  fetchJson: (url: string) => Promise<unknown>,
): Promise<BootContext> {
  const manifest = await fetchJson(MANIFEST_URL)
  if (!Array.isArray(manifest) || !manifest.every((f): f is string => typeof f === 'string')) {
    throw new Error(`theory manifest '${MANIFEST_URL}' must be a JSON array of file-name strings`)
  }
  const loaded: { theory: Theory; ctx: ProofContext }[] = []
  for (const file of manifest) {
    loaded.push(loadTheory(await fetchJson(theoryUrl(file))))
  }
  return mergeTheories(loaded)
}
