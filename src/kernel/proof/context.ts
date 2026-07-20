import type { Diagram } from '../diagram/diagram'
import { mkDiagram } from '../diagram/diagram'
import type { DiagramWithBoundary } from '../diagram/boundary'
import { mkDiagramWithBoundary } from '../diagram/boundary'
import type { Theorem } from './theorem'
import { checkTheorem } from './theorem'
import { ProofError } from './error'

const proofContextBrand: unique symbol = Symbol('ProofContext')

/** A runtime-authenticated, ordered, immutable snapshot of verified proof data. */
export type ProofContext = {
  readonly [proofContextBrand]: true
  readonly theorems: ReadonlyMap<string, Theorem>
  readonly relations: ReadonlyMap<string, DiagramWithBoundary>
}

export type Theory = {
  readonly relations: Readonly<Record<string, DiagramWithBoundary>>
  readonly theorems: readonly Theorem[]
}

class ImmutableMap<K, V> implements ReadonlyMap<K, V> {
  readonly #values: Map<K, V>

  constructor(entries: Iterable<readonly [K, V]>) {
    this.#values = new Map(entries)
    Object.freeze(this)
  }

  get size(): number { return this.#values.size }
  get(key: K): V | undefined { return this.#values.get(key) }
  has(key: K): boolean { return this.#values.has(key) }
  entries(): MapIterator<[K, V]> { return this.#values.entries() }
  keys(): MapIterator<K> { return this.#values.keys() }
  values(): MapIterator<V> { return this.#values.values() }
  forEach(callbackfn: (value: V, key: K, map: ReadonlyMap<K, V>) => void, thisArg?: unknown): void {
    for (const [key, value] of this.#values) callbackfn.call(thisArg, value, key, this)
  }
  [Symbol.iterator](): MapIterator<[K, V]> { return this.entries() }
  get [Symbol.toStringTag](): string { return 'ImmutableMap' }
}

class ImmutableSet<T> implements ReadonlySet<T> {
  readonly #values: Set<T>

  constructor(values: Iterable<T>) {
    this.#values = new Set(values)
    Object.freeze(this)
  }

  get size(): number { return this.#values.size }
  has(value: T): boolean { return this.#values.has(value) }
  entries(): SetIterator<[T, T]> { return this.#values.entries() }
  keys(): SetIterator<T> { return this.#values.keys() }
  values(): SetIterator<T> { return this.#values.values() }
  forEach(callbackfn: (value: T, value2: T, set: ReadonlySet<T>) => void, thisArg?: unknown): void {
    for (const value of this.#values) callbackfn.call(thisArg, value, value, this)
  }
  [Symbol.iterator](): SetIterator<T> { return this.values() }
  get [Symbol.toStringTag](): string { return 'ImmutableSet' }
}

Object.freeze(ImmutableMap.prototype)
Object.freeze(ImmutableSet.prototype)

function immutableClone<T>(value: T, seen = new Map<object, unknown>()): T {
  if (value === null || typeof value !== 'object') return value
  if (value instanceof ImmutableMap || value instanceof ImmutableSet) return value
  const prior = seen.get(value)
  if (prior !== undefined) return prior as T
  if (value instanceof Map) {
    const entries: [unknown, unknown][] = []
    const result = new ImmutableMap(entries)
    seen.set(value, result)
    for (const [key, item] of value) entries.push([immutableClone(key, seen), immutableClone(item, seen)])
    const complete = new ImmutableMap(entries)
    seen.set(value, complete)
    return complete as T
  }
  if (value instanceof Set) {
    const values = [...value].map((item) => immutableClone(item, seen))
    const result = new ImmutableSet(values)
    seen.set(value, result)
    return result as T
  }
  if (Array.isArray(value)) {
    const result: unknown[] = []
    seen.set(value, result)
    for (const item of value) result.push(immutableClone(item, seen))
    return Object.freeze(result) as T
  }
  const result: Record<PropertyKey, unknown> = {}
  seen.set(value, result)
  for (const key of Reflect.ownKeys(value)) {
    result[key] = immutableClone((value as Record<PropertyKey, unknown>)[key], seen)
  }
  return Object.freeze(result) as T
}

const authenticContexts = new WeakSet<object>()

function makeContext(
  theoremEntries: Iterable<readonly [string, Theorem]>,
  relationEntries: Iterable<readonly [string, DiagramWithBoundary]>,
): ProofContext {
  const context = Object.freeze({
    [proofContextBrand]: true as const,
    theorems: new ImmutableMap(theoremEntries),
    relations: new ImmutableMap(relationEntries),
  })
  authenticContexts.add(context)
  return context
}

export const EMPTY_PROOF_CONTEXT: ProofContext = makeContext([], [])

export function assertProofContext(value: unknown): asserts value is ProofContext {
  if (typeof value !== 'object' || value === null || !authenticContexts.has(value)) {
    throw new ProofError('invalid proof context')
  }
}

function checkedBoundary(value: DiagramWithBoundary, where: string): DiagramWithBoundary {
  try {
    const copy = immutableClone(value)
    const diagram = mkDiagram({
      root: copy.diagram.root,
      regions: copy.diagram.regions,
      nodes: copy.diagram.nodes,
      wires: copy.diagram.wires,
    })
    const checked = mkDiagramWithBoundary(diagram, copy.boundary)
    for (const wire of checked.boundary) {
      if (checked.diagram.wires[wire]!.scope !== checked.diagram.root) {
        throw new Error(`boundary wire '${wire}' is not scoped at the diagram root`)
      }
    }
    return immutableClone(checked)
  } catch (error) {
    throw new ProofError(`${where}: ${error instanceof Error ? error.message : String(error)}`)
  }
}

/** Every ref node must resolve against exactly the supplied relation prefix. */
export function assertRefsResolve(
  diagram: Diagram,
  relationArities: ReadonlyMap<string, number>,
  where: string,
): void {
  for (const [id, node] of Object.entries(diagram.nodes)) {
    if (node.kind !== 'ref') continue
    const arity = relationArities.get(node.defId)
    if (arity === undefined) {
      throw new ProofError(`${where}: reference node '${id}' names unknown relation '${node.defId}'`)
    }
    if (arity !== node.arity) {
      throw new ProofError(
        `${where}: reference node '${id}' to relation '${node.defId}' has arity ${node.arity} but the relation has arity ${arity}`,
      )
    }
  }
}

function relationArities(ctx: ProofContext): Map<string, number> {
  return new Map([...ctx.relations].map(([name, relation]) => [name, relation.boundary.length]))
}

/** Append definitions in order, checking each body only against its prior prefix. */
export function extendRelations(
  base: ProofContext,
  entries: Iterable<readonly [string, DiagramWithBoundary]>,
): ProofContext {
  assertProofContext(base)
  const additions = [...entries]
  if (additions.length === 0) return base
  if (base.theorems.size > 0) {
    throw new ProofError('relations cannot be added after theorem registration')
  }
  const relations = new Map(base.relations)
  const arities = relationArities(base)
  for (const [name, value] of additions) {
    if (relations.has(name) || base.theorems.has(name)) {
      throw new ProofError(`duplicate proof-context name '${name}'`)
    }
    const relation = checkedBoundary(value, `relation '${name}'`)
    assertRefsResolve(relation.diagram, arities, `relation '${name}' body`)
    relations.set(name, relation)
    arities.set(name, relation.boundary.length)
  }
  return makeContext(base.theorems, relations)
}

function checkedTheorem(value: Theorem): Theorem {
  const copy = immutableClone(value)
  return immutableClone({
    ...copy,
    lhs: checkedBoundary(copy.lhs, `theorem '${copy.name}' left-hand side`),
    rhs: checkedBoundary(copy.rhs, `theorem '${copy.name}' right-hand side`),
  })
}

/** Verify and append one theorem against the existing theorem prefix. */
export function registerTheorem(base: ProofContext, value: Theorem): ProofContext {
  assertProofContext(base)
  const theorem = checkedTheorem(value)
  if (base.theorems.has(theorem.name)) throw new ProofError(`duplicate theorem name '${theorem.name}'`)
  if (base.relations.has(theorem.name)) throw new ProofError(`duplicate proof-context name '${theorem.name}'`)
  const arities = relationArities(base)
  assertRefsResolve(theorem.lhs.diagram, arities, `theorem '${theorem.name}' left-hand side`)
  assertRefsResolve(theorem.rhs.diagram, arities, `theorem '${theorem.name}' right-hand side`)
  checkTheorem(theorem, base)
  return makeContext([...base.theorems, [theorem.name, theorem]], base.relations)
}

/** Verify a complete ordered theory through the same incremental authority. */
export function verifyTheory(theory: Theory): ProofContext {
  const relationEntries = Object.entries(theory.relations)
  if (relationEntries.length === 0 && theory.theorems.length === 0) return EMPTY_PROOF_CONTEXT
  let context = extendRelations(EMPTY_PROOF_CONTEXT, relationEntries)
  for (const theorem of theory.theorems) context = registerTheorem(context, theorem)
  return context
}
