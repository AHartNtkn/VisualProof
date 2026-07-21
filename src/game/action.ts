import type { ProofAction } from '../kernel/proof/action'
import { actionFromJson, actionToJson } from '../kernel/proof/json'
import type { SubgraphSelection } from '../kernel/diagram/subgraph/selection'
import { type ArtifactAction } from './artifact'
import type { GameSessionAction } from './session'
import { GameDomainError, puzzleId } from './types'

export type SerializedGameSessionAction = Readonly<Record<string, unknown>>

const immutableActionSnapshot = <T>(value: T, active: object[] = []): T => {
  if (value === null || value === undefined) return value
  const kind = typeof value
  if (kind === 'string' || kind === 'boolean') return value
  if (kind === 'number') {
    if (!Number.isFinite(value)) throw new GameDomainError('game session action numbers must be finite')
    return value
  }
  if (kind !== 'object') throw new GameDomainError(`game session action contains unsupported ${kind} data`)
  const source = value as object
  if (active.includes(source)) throw new GameDomainError('game session action must not be cyclic')
  active.push(source)
  try {
    if (Array.isArray(value)) {
      return Object.freeze(value.map((entry) => immutableActionSnapshot(entry, active))) as T
    }
    if (value instanceof Map) {
      const copy = new Map([...value].map(([key, entry]) => [
        immutableActionSnapshot(key, active),
        immutableActionSnapshot(entry, active),
      ]))
      Object.defineProperties(copy, {
        set: { value: () => { throw new GameDomainError('stored game session action is immutable') } },
        delete: { value: () => { throw new GameDomainError('stored game session action is immutable') } },
        clear: { value: () => { throw new GameDomainError('stored game session action is immutable') } },
      })
      return Object.freeze(copy) as T
    }
    if (value instanceof Set) {
      const copy = new Set([...value].map((entry) => immutableActionSnapshot(entry, active)))
      Object.defineProperties(copy, {
        add: { value: () => { throw new GameDomainError('stored game session action is immutable') } },
        delete: { value: () => { throw new GameDomainError('stored game session action is immutable') } },
        clear: { value: () => { throw new GameDomainError('stored game session action is immutable') } },
      })
      return Object.freeze(copy) as T
    }
    const prototype = Object.getPrototypeOf(value)
    if (prototype !== Object.prototype && prototype !== null) {
      throw new GameDomainError('game session action contains an unsupported object type')
    }
    const copy: Record<string, unknown> = {}
    for (const key of Reflect.ownKeys(value)) {
      if (typeof key !== 'string') throw new GameDomainError('game session action fields must be strings')
      const descriptor = Object.getOwnPropertyDescriptor(value, key)
      if (descriptor === undefined || !('value' in descriptor)) {
        throw new GameDomainError('game session action must not contain accessor fields')
      }
      copy[key] = immutableActionSnapshot(descriptor.value, active)
    }
    return Object.freeze(copy) as T
  } finally {
    active.pop()
  }
}

export function snapshotGameSessionAction(action: GameSessionAction): GameSessionAction {
  const parsed = record(action, 'game session action')
  const allowed = 'kind' in parsed
    ? parsed.kind === 'artifactManifest'
      ? ['kind', 'artifact', 'region']
      : parsed.kind === 'artifactDissolve'
        ? ['kind', 'artifact', 'selection']
        : []
    : ['label', 'steps', 'placements', 'allocation']
  if (allowed.length === 0) throw new GameDomainError(`game session action has unknown kind '${String(parsed.kind)}'`)
  only(parsed, allowed, 'game session action')
  return immutableActionSnapshot(action)
}

const record = (value: unknown, label: string): Record<string, unknown> => {
  if (typeof value !== 'object' || value === null || Array.isArray(value)) {
    throw new GameDomainError(`${label} must be an object`)
  }
  return value as Record<string, unknown>
}

const only = (value: Record<string, unknown>, fields: readonly string[], label: string): void => {
  for (const key of Object.keys(value)) {
    if (!fields.includes(key)) throw new GameDomainError(`${label} has unknown field '${key}'`)
  }
}

const string = (value: unknown, label: string): string => {
  if (typeof value !== 'string' || value.length === 0) {
    throw new GameDomainError(`${label} must be a non-empty string`)
  }
  return value
}

const strings = (value: unknown, label: string): readonly string[] => {
  if (!Array.isArray(value)) throw new GameDomainError(`${label} must be an array`)
  return value.map((item, index) => string(item, `${label}[${index}]`))
}

const selectionFromJson = (value: unknown, label: string): SubgraphSelection => {
  const parsed = record(value, label)
  only(parsed, ['region', 'regions', 'nodes', 'wires'], label)
  return {
    region: string(parsed.region, `${label}.region`),
    regions: strings(parsed.regions, `${label}.regions`),
    nodes: strings(parsed.nodes, `${label}.nodes`),
    wires: strings(parsed.wires, `${label}.wires`),
  }
}

export function gameSessionActionToJson(
  action: GameSessionAction,
): SerializedGameSessionAction {
  if ('kind' in action) {
    if (action.kind === 'artifactManifest') {
      return { kind: action.kind, artifact: action.artifact, region: action.region }
    }
    return {
      kind: action.kind,
      artifact: action.artifact,
      selection: {
        region: action.selection.region,
        regions: [...action.selection.regions],
        nodes: [...action.selection.nodes],
        wires: [...action.selection.wires],
      },
    }
  }
  return record(actionToJson(action), 'serialized proof action')
}

export function gameSessionActionFromJson(
  value: unknown,
  label = 'game session action',
): GameSessionAction {
  const parsed = record(value, label)
  if (parsed.kind === 'artifactManifest') {
    only(parsed, ['kind', 'artifact', 'region'], label)
    return {
      kind: 'artifactManifest',
      artifact: puzzleId(string(parsed.artifact, `${label}.artifact`)),
      region: string(parsed.region, `${label}.region`),
    }
  }
  if (parsed.kind === 'artifactDissolve') {
    only(parsed, ['kind', 'artifact', 'selection'], label)
    return {
      kind: 'artifactDissolve',
      artifact: puzzleId(string(parsed.artifact, `${label}.artifact`)),
      selection: selectionFromJson(parsed.selection, `${label}.selection`),
    }
  }
  if ('kind' in parsed) {
    throw new GameDomainError(`${label} has unknown kind '${String(parsed.kind)}'`)
  }
  try {
    return actionFromJson(value, label) as ProofAction
  } catch (error) {
    throw new GameDomainError(
      `invalid ${label}: ${error instanceof Error ? error.message : String(error)}`,
    )
  }
}

export const artifactActionRule = (action: ArtifactAction): ArtifactAction['kind'] => action.kind
