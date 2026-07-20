import type { DiagramWithBoundary } from '../diagram/boundary'
import type { ProofContext, Theory } from './context'
import { verifyTheory } from './context'
import { dwbToJson, dwbFromJson, theoremToJson, theoremFromJson } from './json'

/**
 * A theory: named relations (comprehensions) and theorems in registration
 * order — later theorems may cite earlier ones by name. Semantic content only
 * (layer separation: no layout, no physics, ever).
 */
export type { Theory } from './context'
export { assertRefsResolve, verifyTheory } from './context'

const FORMAT = 'visual-proof-theory'
const VERSION = 1

export function theoryToJson(t: Theory): unknown {
  const relations: Record<string, unknown> = {}
  for (const [name, rel] of Object.entries(t.relations)) relations[name] = dwbToJson(rel)
  return {
    format: FORMAT,
    version: VERSION,
    relations,
    theorems: t.theorems.map(theoremToJson),
  }
}

function fail(msg: string): never {
  throw new Error(`malformed theory JSON: ${msg}`)
}

function isRecord(v: unknown): v is Record<string, unknown> {
  return typeof v === 'object' && v !== null && !Array.isArray(v)
}

export function theoryFromJson(j: unknown): Theory {
  if (!isRecord(j)) fail('top level must be an object')
  for (const k of Object.keys(j)) {
    if (!['format', 'version', 'relations', 'theorems'].includes(k)) {
      fail(`top level has unknown field '${k}' (semantic files carry no extra data)`)
    }
  }
  if (j.format !== FORMAT) fail(`unrecognized format '${String(j.format)}'`)
  if (j.version !== VERSION) fail(`unsupported version '${String(j.version)}' (expected ${VERSION})`)
  if (!isRecord(j.relations) || !Array.isArray(j.theorems)) {
    fail("'relations' must be an object and 'theorems' an array")
  }
  const relations: Record<string, DiagramWithBoundary> = {}
  for (const [name, v] of Object.entries(j.relations)) {
    relations[name] = dwbFromJson(v, `relation '${name}'`)
  }
  return { relations, theorems: j.theorems.map((t) => theoremFromJson(t)) }
}

/** Parse + verify: the only way to bring a theory file into the kernel. */
export function loadTheory(j: unknown): { theory: Theory; ctx: ProofContext } {
  const theory = theoryFromJson(j)
  return { theory, ctx: verifyTheory(theory) }
}
