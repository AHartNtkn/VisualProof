import type { Term } from '../term/term'
import { serializeTerm, deserializeTerm } from '../term/serialize'
import type { DiagramWithBoundary } from '../diagram/boundary'
import { mkDiagramWithBoundary } from '../diagram/boundary'
import type { Definitions } from '../rules/definitions'
import { assertWellFormedDefinitions } from '../rules/definitions'
import type { ProofContext } from './step'
import type { Theorem } from './theorem'
import { checkTheorem } from './theorem'
import { dwbToJson, dwbFromJson, theoremToJson, theoremFromJson } from './json'
import { ProofError } from './error'

/**
 * A theory: definitions, named relations (comprehensions), and theorems in
 * registration order — later theorems may cite earlier ones by name. Semantic
 * content only (layer separation: no layout, no physics, ever).
 */
export type Theory = {
  readonly definitions: Definitions
  readonly relations: Readonly<Record<string, DiagramWithBoundary>>
  readonly theorems: readonly Theorem[]
}

/** Verify everything; returns the full proof context. There is no trust-without-verify path. */
export function verifyTheory(t: Theory): ProofContext {
  assertWellFormedDefinitions(t.definitions)
  for (const [name, rel] of Object.entries(t.relations)) {
    try {
      mkDiagramWithBoundary(rel.diagram, rel.boundary) // re-validates boundary existence/uniqueness
    } catch (e) {
      throw new ProofError(`relation '${name}': ${e instanceof Error ? e.message : String(e)}`)
    }
  }
  const theorems = new Map<string, Theorem>()
  for (const thm of t.theorems) {
    if (theorems.has(thm.name)) throw new ProofError(`duplicate theorem name '${thm.name}'`)
    checkTheorem(thm, { definitions: t.definitions, theorems })
    theorems.set(thm.name, thm)
  }
  return { definitions: t.definitions, theorems }
}

const FORMAT = 'visual-proof-theory'
const VERSION = 1

export function theoryToJson(t: Theory): unknown {
  const definitions: Record<string, string> = {}
  for (const [id, body] of Object.entries(t.definitions)) definitions[id] = serializeTerm(body)
  const relations: Record<string, unknown> = {}
  for (const [name, rel] of Object.entries(t.relations)) relations[name] = dwbToJson(rel)
  return {
    format: FORMAT,
    version: VERSION,
    definitions,
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
    if (!['format', 'version', 'definitions', 'relations', 'theorems'].includes(k)) {
      fail(`top level has unknown field '${k}' (semantic files carry no extra data)`)
    }
  }
  if (j.format !== FORMAT) fail(`unrecognized format '${String(j.format)}'`)
  if (j.version !== VERSION) fail(`unsupported version '${String(j.version)}' (expected ${VERSION})`)
  if (!isRecord(j.definitions) || !isRecord(j.relations) || !Array.isArray(j.theorems)) {
    fail("'definitions'/'relations' must be objects and 'theorems' an array")
  }
  const definitions: Record<string, Term> = {}
  for (const [id, v] of Object.entries(j.definitions)) {
    if (typeof v !== 'string') fail(`definition '${id}' must be a serialized term string`)
    try {
      definitions[id] = deserializeTerm(v)
    } catch (e) {
      fail(`definition '${id}': ${e instanceof Error ? e.message : String(e)}`)
    }
  }
  const relations: Record<string, DiagramWithBoundary> = {}
  for (const [name, v] of Object.entries(j.relations)) {
    relations[name] = dwbFromJson(v, `relation '${name}'`)
  }
  return { definitions, relations, theorems: j.theorems.map((t) => theoremFromJson(t)) }
}

/** Parse + verify: the only way to bring a theory file into the kernel. */
export function loadTheory(j: unknown): { theory: Theory; ctx: ProofContext } {
  const theory = theoryFromJson(j)
  return { theory, ctx: verifyTheory(theory) }
}
