import type { Diagram } from '../diagram/diagram'
import type { DiagramWithBoundary } from '../diagram/boundary'
import { mkDiagramWithBoundary } from '../diagram/boundary'
import type { ProofContext } from './step'
import type { Theorem } from './theorem'
import { checkTheorem } from './theorem'
import { dwbToJson, dwbFromJson, theoremToJson, theoremFromJson } from './json'
import { ProofError } from './error'

/**
 * A theory: named relations (comprehensions) and theorems in registration
 * order — later theorems may cite earlier ones by name. Semantic content only
 * (layer separation: no layout, no physics, ever).
 */
export type Theory = {
  readonly relations: Readonly<Record<string, DiagramWithBoundary>>
  readonly theorems: readonly Theorem[]
}

/**
 * Every ref node in `d` must resolve against `relArity`: its defId names a
 * relation whose arity equals the ref's. `where` names the diagram for the
 * refusal (a theorem side or a relation body).
 */
function assertRefsResolve(d: Diagram, relArity: ReadonlyMap<string, number>, where: string): void {
  for (const [id, n] of Object.entries(d.nodes)) {
    if (n.kind !== 'ref') continue
    const arity = relArity.get(n.defId)
    if (arity === undefined) {
      throw new ProofError(`${where}: reference node '${id}' names unknown relation '${n.defId}'`)
    }
    if (arity !== n.arity) {
      throw new ProofError(
        `${where}: reference node '${id}' to relation '${n.defId}' has arity ${n.arity} but the relation has arity ${arity}`,
      )
    }
  }
}

/** Verify everything; returns the full proof context. There is no trust-without-verify path. */
export function verifyTheory(t: Theory): ProofContext {
  const relations = new Map<string, DiagramWithBoundary>()
  const relArity = new Map<string, number>()
  for (const [name, rel] of Object.entries(t.relations)) {
    try {
      mkDiagramWithBoundary(rel.diagram, rel.boundary) // re-validates boundary existence/uniqueness
    } catch (e) {
      throw new ProofError(`relation '${name}': ${e instanceof Error ? e.message : String(e)}`)
    }
    // No self-containedness check is needed: a stored relation body is closed by
    // construction (a DiagramWithBoundary is a self-contained diagram). Openness
    // is not a property of a stored body at all — it exists only as a splice-time
    // binder map deciding which bubbles are external stubs, and relUnfold always
    // splices with an EMPTY binder map, so every bubble in a body is content with
    // ∃-meaning and is copied soundly. A body like R(x) := ∃S[S(x)] with a
    // top-level bubble is therefore perfectly legitimate.
    relations.set(name, rel)
    relArity.set(name, rel.boundary.length)
  }
  for (const [name, rel] of relations) {
    assertRefsResolve(rel.diagram, relArity, `relation '${name}' body`)
  }
  const theorems = new Map<string, Theorem>()
  for (const thm of t.theorems) {
    if (theorems.has(thm.name)) throw new ProofError(`duplicate theorem name '${thm.name}'`)
    assertRefsResolve(thm.lhs.diagram, relArity, `theorem '${thm.name}' left-hand side`)
    assertRefsResolve(thm.rhs.diagram, relArity, `theorem '${thm.name}' right-hand side`)
    checkTheorem(thm, { theorems, relations })
    theorems.set(thm.name, thm)
  }
  return { theorems, relations }
}

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
