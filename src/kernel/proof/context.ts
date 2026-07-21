import type { Diagram } from '../diagram/diagram'
import type { DiagramWithBoundary } from '../diagram/boundary'
import type { Theorem } from './theorem'
import { checkTheorem } from './theorem'
import { dwbFromJson, dwbToJson, theoremFromJson, theoremToJson } from './json'
import { ProofError } from './error'

const proofContextBrand: unique symbol = Symbol('ProofContext')

/** A runtime-authenticated, ordered, immutable snapshot of verified proof data. */
export type ProofContext = {
  readonly [proofContextBrand]: true
  readonly theorems: ReadonlyMap<string, Theorem>
  readonly relations: ReadonlyMap<string, DiagramWithBoundary>
}

/** Relations are an explicit sequence: their order is part of verification. */
export type Theory = {
  readonly relations: readonly (readonly [string, DiagramWithBoundary])[]
  readonly theorems: readonly Theorem[]
}

function immutableIterator<T>(values: readonly T[]): MapIterator<T> {
  let index = 0
  const iterator = {
    next: (): IteratorResult<T> => index < values.length
      ? { done: false, value: values[index++]! }
      : { done: true, value: undefined },
    [Symbol.iterator](): MapIterator<T> { return iterator as MapIterator<T> },
    [Symbol.dispose](): void {},
  }
  return Object.freeze(iterator) as MapIterator<T>
}

/** No native Map lookup or iterator is consulted after construction. */
class ImmutableMap<K, V> implements ReadonlyMap<K, V> {
  readonly #entries: readonly (readonly [K, V])[]

  constructor(entries: Iterable<readonly [K, V]>) {
    const copy: Array<readonly [K, V]> = []
    for (const [key, value] of entries) copy[copy.length] = Object.freeze([key, value] as const)
    this.#entries = Object.freeze(copy)
    Object.freeze(this)
  }

  get size(): number { return this.#entries.length }
  get(key: K): V | undefined {
    for (let index = 0; index < this.#entries.length; index += 1) {
      const entry = this.#entries[index]!
      if (sameValueZero(entry[0], key)) return entry[1]
    }
    return undefined
  }
  has(key: K): boolean {
    for (let index = 0; index < this.#entries.length; index += 1) {
      const candidate = this.#entries[index]![0]
      if (sameValueZero(candidate, key)) return true
    }
    return false
  }
  entries(): MapIterator<[K, V]> {
    const values: [K, V][] = []
    for (let index = 0; index < this.#entries.length; index += 1) {
      const [key, value] = this.#entries[index]!
      values[values.length] = [key, value]
    }
    return immutableIterator(values)
  }
  keys(): MapIterator<K> {
    const values: K[] = []
    for (let index = 0; index < this.#entries.length; index += 1) values[values.length] = this.#entries[index]![0]
    return immutableIterator(values)
  }
  values(): MapIterator<V> {
    const values: V[] = []
    for (let index = 0; index < this.#entries.length; index += 1) values[values.length] = this.#entries[index]![1]
    return immutableIterator(values)
  }
  forEach(callbackfn: (value: V, key: K, map: ReadonlyMap<K, V>) => void, thisArg?: unknown): void {
    for (let index = 0; index < this.#entries.length; index += 1) {
      const [key, value] = this.#entries[index]!
      callbackfn.call(thisArg, value, key, this)
    }
  }
  [Symbol.iterator](): MapIterator<[K, V]> { return this.entries() }
  get [Symbol.toStringTag](): string { return 'ImmutableMap' }
}

class ImmutableSet<T> implements ReadonlySet<T> {
  readonly #values: readonly T[]

  constructor(values: Iterable<T>) {
    const copy: T[] = []
    for (const value of values) copy[copy.length] = value
    this.#values = Object.freeze(copy)
    Object.freeze(this)
  }

  get size(): number { return this.#values.length }
  has(value: T): boolean {
    for (let index = 0; index < this.#values.length; index += 1) {
      const candidate = this.#values[index]!
      if (sameValueZero(candidate, value)) return true
    }
    return false
  }
  entries(): SetIterator<[T, T]> {
    const values: [T, T][] = []
    for (let index = 0; index < this.#values.length; index += 1) {
      const value = this.#values[index]!
      values[values.length] = [value, value]
    }
    return immutableIterator(values) as SetIterator<[T, T]>
  }
  keys(): SetIterator<T> { return immutableIterator(this.#values) as SetIterator<T> }
  values(): SetIterator<T> { return immutableIterator(this.#values) as SetIterator<T> }
  forEach(callbackfn: (value: T, value2: T, set: ReadonlySet<T>) => void, thisArg?: unknown): void {
    for (let index = 0; index < this.#values.length; index += 1) {
      const value = this.#values[index]!
      callbackfn.call(thisArg, value, value, this)
    }
  }
  [Symbol.iterator](): SetIterator<T> { return this.values() }
  get [Symbol.toStringTag](): string { return 'ImmutableSet' }
}

Object.freeze(ImmutableMap.prototype)
Object.freeze(ImmutableSet.prototype)

function sameValueZero(left: unknown, right: unknown): boolean {
  return left === right || (left !== left && right !== right)
}

const ownKeys = Reflect.ownKeys
const getOwnPropertyDescriptor = Object.getOwnPropertyDescriptor
const getPrototypeOf = Object.getPrototypeOf
const setPrototypeOf = Object.setPrototypeOf
const mapEntriesIntrinsic = Function.prototype.call.bind(Map.prototype.entries) as <K, V>(map: Map<K, V>) => MapIterator<[K, V]>
const setValuesIntrinsic = Function.prototype.call.bind(Set.prototype.values) as <T>(set: Set<T>) => SetIterator<T>
const mapIteratorNextIntrinsic = Function.prototype.call.bind(getPrototypeOf(new Map().entries()).next) as <K, V>(iterator: MapIterator<[K, V]>) => IteratorResult<[K, V]>
const setIteratorNextIntrinsic = Function.prototype.call.bind(getPrototypeOf(new Set().values()).next) as <T>(iterator: SetIterator<T>) => IteratorResult<T>

/** Reject executable, exotic, accessor, and cyclic values before a codec reads them. */
function assertSchemaCarrier(value: unknown, where: string, active: object[] = []): void {
  if (value === null || value === undefined) return
  const kind = typeof value
  if (kind === 'string' || kind === 'boolean') return
  if (kind === 'number') {
    if (!Number.isFinite(value)) throw new ProofError(`${where}: numbers must be finite`)
    return
  }
  if (kind !== 'object') throw new ProofError(`${where}: unsupported ${kind} value`)
  const object = value as object
  for (let index = 0; index < active.length; index += 1) {
    if (active[index] === object) throw new ProofError(`${where}: cyclic values are not supported`)
  }
  active.push(object)
  try {
    if (value instanceof ImmutableMap) {
      for (const [key, item] of value) {
        assertSchemaCarrier(key, where, active)
        assertSchemaCarrier(item, where, active)
      }
      return
    }
    if (value instanceof ImmutableSet) {
      for (const item of value) assertSchemaCarrier(item, where, active)
      return
    }
    if (value instanceof Map) {
      const iterator = mapEntriesIntrinsic(value)
      for (;;) {
        const next = mapIteratorNextIntrinsic(iterator)
        if (next.done) break
        assertSchemaCarrier(next.value[0], where, active)
        assertSchemaCarrier(next.value[1], where, active)
      }
      return
    }
    if (value instanceof Set) {
      const iterator = setValuesIntrinsic(value)
      for (;;) {
        const next = setIteratorNextIntrinsic(iterator)
        if (next.done) break
        assertSchemaCarrier(next.value, where, active)
      }
      return
    }
    if (!Array.isArray(value) && getPrototypeOf(value) !== Object.prototype && getPrototypeOf(value) !== null) {
      throw new ProofError(`${where}: unsupported object type`)
    }
    const keys = ownKeys(object)
    for (let index = 0; index < keys.length; index += 1) {
      const key = keys[index]!
      const descriptor = getOwnPropertyDescriptor(object, key)
      if (descriptor === undefined || !('value' in descriptor)) {
        throw new ProofError(`${where}: accessor properties are not supported`)
      }
      assertSchemaCarrier(descriptor.value, where, active)
    }
  } finally {
    active.pop()
  }
}

/** Harden codec-produced, acyclic schema data without exposing native collections. */
function immutableClone<T>(value: T): T {
  if (value === null || value === undefined || typeof value !== 'object') return value
  if (value instanceof ImmutableMap || value instanceof ImmutableSet) return value
  if (value instanceof Map) {
    const entries: Array<readonly [unknown, unknown]> = []
    const iterator = mapEntriesIntrinsic(value)
    for (;;) {
      const next = mapIteratorNextIntrinsic(iterator)
      if (next.done) break
      entries[entries.length] = [immutableClone(next.value[0]), immutableClone(next.value[1])]
    }
    return new ImmutableMap(entries) as T
  }
  if (value instanceof Set) {
    const values: unknown[] = []
    const iterator = setValuesIntrinsic(value)
    for (;;) {
      const next = setIteratorNextIntrinsic(iterator)
      if (next.done) break
      values[values.length] = immutableClone(next.value)
    }
    return new ImmutableSet(values) as T
  }
  if (Array.isArray(value)) {
    const result: unknown[] = []
    for (let index = 0; index < value.length; index += 1) result[result.length] = immutableClone(value[index])
    return Object.freeze(result) as T
  }
  const result: Record<PropertyKey, unknown> = Object.create(null)
  const keys = ownKeys(value)
  for (let index = 0; index < keys.length; index += 1) {
    const key = keys[index]!
    const descriptor = getOwnPropertyDescriptor(value, key)!
    result[key] = immutableClone(descriptor.value)
  }
  return Object.freeze(result) as T
}

const contextCapability = Object.freeze(Object.create(null))

class ContextValue implements ProofContext {
  readonly #authenticated = true
  readonly [proofContextBrand] = true as const
  readonly theorems: ReadonlyMap<string, Theorem>
  readonly relations: ReadonlyMap<string, DiagramWithBoundary>

  constructor(
    capability: object,
    theoremEntries: Iterable<readonly [string, Theorem]>,
    relationEntries: Iterable<readonly [string, DiagramWithBoundary]>,
  ) {
    if (capability !== contextCapability) throw new ProofError('invalid proof context construction')
    this.theorems = new ImmutableMap(theoremEntries)
    this.relations = new ImmutableMap(relationEntries)
    setPrototypeOf(this, null)
    Object.freeze(this)
  }

  static authentic(value: object): value is ContextValue { return #authenticated in value }
}

Object.freeze(ContextValue.prototype)
Object.freeze(ContextValue)

function makeContext(
  theoremEntries: Iterable<readonly [string, Theorem]>,
  relationEntries: Iterable<readonly [string, DiagramWithBoundary]>,
): ProofContext {
  return new ContextValue(contextCapability, theoremEntries, relationEntries)
}

export const EMPTY_PROOF_CONTEXT: ProofContext = makeContext([], [])

export function assertProofContext(value: unknown): asserts value is ProofContext {
  if (typeof value !== 'object' || value === null || !ContextValue.authentic(value)) {
    throw new ProofError('invalid proof context')
  }
}

function checkedBoundary(value: DiagramWithBoundary, where: string): DiagramWithBoundary {
  try {
    assertSchemaCarrier(value, where)
    const checked = immutableClone(dwbFromJson(dwbToJson(value), where))
    for (const wire of checked.boundary) {
      if (checked.diagram.wires[wire]!.scope !== checked.diagram.root) {
        throw new Error(`boundary wire '${wire}' is not scoped at the diagram root`)
      }
    }
    return checked
  } catch (error) {
    if (error instanceof ProofError) throw error
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

function relationArities(ctx: ProofContext): ImmutableMap<string, number> {
  const entries: Array<readonly [string, number]> = []
  for (const [name, relation] of ctx.relations) entries[entries.length] = [name, relation.boundary.length]
  return new ImmutableMap(entries)
}

/** Append definitions in order, checking each body only against its prior prefix. */
export function extendRelations(
  base: ProofContext,
  entries: Iterable<readonly [string, DiagramWithBoundary]>,
): ProofContext {
  assertProofContext(base)
  const additions = Array.from(entries)
  if (additions.length === 0) return base
  if (base.theorems.size > 0) {
    throw new ProofError('relations cannot be added after theorem registration')
  }
  const relations: Array<readonly [string, DiagramWithBoundary]> = Array.from(base.relations)
  const arities: Array<readonly [string, number]> = []
  for (const [name, relation] of base.relations) arities[arities.length] = [name, relation.boundary.length]
  for (const [name, value] of additions) {
    const relationPrefix = new ImmutableMap(relations)
    if (relationPrefix.has(name) || base.theorems.has(name)) {
      throw new ProofError(`duplicate proof-context name '${name}'`)
    }
    const relation = checkedBoundary(value, `relation '${name}'`)
    assertRefsResolve(relation.diagram, new ImmutableMap(arities), `relation '${name}' body`)
    relations[relations.length] = [name, relation]
    arities[arities.length] = [name, relation.boundary.length]
  }
  return makeContext(base.theorems, relations)
}

function checkedTheorem(value: Theorem): Theorem {
  try {
    assertSchemaCarrier(value, 'theorem')
    // The codec is the complete serialized theorem schema validator. Keep the
    // already-validated witness maps in their original insertion order: their
    // order carries lexical binder-spine evidence and is not presentation data.
    theoremFromJson(theoremToJson(value))
    const theorem = immutableClone(value)
    return immutableClone({
      ...theorem,
      lhs: checkedBoundary(theorem.lhs, `theorem '${theorem.name}' left-hand side`),
      rhs: checkedBoundary(theorem.rhs, `theorem '${theorem.name}' right-hand side`),
    })
  } catch (error) {
    if (error instanceof ProofError) throw error
    throw new ProofError(`invalid theorem: ${error instanceof Error ? error.message : String(error)}`)
  }
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
  if (theory.relations.length === 0 && theory.theorems.length === 0) return EMPTY_PROOF_CONTEXT
  let context = extendRelations(EMPTY_PROOF_CONTEXT, theory.relations)
  for (const theorem of theory.theorems) context = registerTheorem(context, theorem)
  return context
}
