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
  return {
    format: FORMAT,
    version: VERSION,
    relations: t.relations.map(([name, relation]) => [name, dwbToJson(relation)]),
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
  if (!Array.isArray(j.relations) || !Array.isArray(j.theorems)) {
    fail("'relations' and 'theorems' must be arrays")
  }
  const relations: Array<readonly [string, DiagramWithBoundary]> = []
  const names = new Set<string>()
  for (const [index, entry] of j.relations.entries()) {
    if (!Array.isArray(entry) || entry.length !== 2 || typeof entry[0] !== 'string') {
      fail(`relations[${index}] must be a [name, body] pair`)
    }
    const name = entry[0]
    if (names.has(name)) fail(`relations repeats name '${name}'`)
    names.add(name)
    relations.push([name, dwbFromJson(entry[1], `relation '${name}'`)])
  }
  return { relations, theorems: j.theorems.map((t) => theoremFromJson(t)) }
}

/** Parse + verify: the only way to bring a theory file into the kernel. */
export function loadTheory(j: unknown): { theory: Theory; ctx: ProofContext } {
  const theory = theoryFromJson(j)
  return { theory, ctx: verifyTheory(theory) }
}
