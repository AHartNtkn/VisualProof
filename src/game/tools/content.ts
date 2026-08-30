import openingToolContentJson from '../../../game/content/tools.json?raw'
import type { ToolId } from '../tools'

export type ToolContentDefinition = {
  readonly id: ToolId
  readonly name: string
  readonly description: string
}

export type ToolContentRevision = {
  readonly definitions: readonly ToolContentDefinition[]
  definition(id: string): ToolContentDefinition
}

const visibleToolIds: readonly ToolId[] = ['sprout-spawner', 'double-cut', 'iteration']
const visibleToolIdSet = new Set<string>(visibleToolIds)
const decodedRevisions = new WeakSet<ToolContentRevision>()

function record(value: unknown, what: string): Record<string, unknown> {
  if (typeof value !== 'object' || value === null || Array.isArray(value)) {
    throw new Error(`${what} must be an object`)
  }
  return value as Record<string, unknown>
}

function nonblankString(value: unknown, what: string): string {
  if (typeof value !== 'string' || value.trim() === '') throw new Error(`${what} must be non-blank`)
  return value
}

function decodeDefinition(value: unknown, index: number): ToolContentDefinition {
  const raw = record(value, `tool content ${index}`)
  for (const key of Object.keys(raw)) {
    if (key !== 'id' && key !== 'name' && key !== 'description') {
      throw new Error(`tool content ${index} has unknown field '${key}'`)
    }
  }
  if (!Object.hasOwn(raw, 'id') || !Object.hasOwn(raw, 'name') || !Object.hasOwn(raw, 'description')) {
    throw new Error(`tool content ${index} must contain id, name, and description`)
  }
  const id = nonblankString(raw['id'], `tool content ${index}.id`)
  if (!visibleToolIdSet.has(id)) throw new Error(`tool content has unknown tool '${id}'`)
  return Object.freeze({
    id: id as ToolId,
    name: nonblankString(raw['name'], `tool content ${index}.name`),
    description: nonblankString(raw['description'], `tool content ${index}.description`),
  })
}

export function decodeToolContent(raw: unknown): ToolContentRevision {
  if (!Array.isArray(raw)) throw new Error('tool content must be an array')
  const definitions = raw.map(decodeDefinition)
  const byId = new Map<ToolId, ToolContentDefinition>()
  for (const definition of definitions) {
    if (byId.has(definition.id)) throw new Error(`tool content has duplicate tool '${definition.id}'`)
    byId.set(definition.id, definition)
  }
  for (const id of visibleToolIds) {
    if (!byId.has(id)) throw new Error(`tool content is missing tool '${id}'`)
  }
  const revision: ToolContentRevision = Object.freeze({
    definitions: Object.freeze(definitions),
    definition(id: string): ToolContentDefinition {
      const definition = byId.get(id as ToolId)
      if (definition === undefined) throw new Error(`unknown tool '${id}'`)
      return definition
    },
  })
  decodedRevisions.add(revision)
  return revision
}

export class LiveToolContent {
  public constructor(private revisionValue: ToolContentRevision) {
    if (!decodedRevisions.has(revisionValue)) throw new Error('live tool content requires a decoded revision')
  }

  public get current(): ToolContentRevision {
    return this.revisionValue
  }

  public publish(next: ToolContentRevision): void {
    if (!decodedRevisions.has(next)) throw new Error('live tool content requires a decoded revision')
    this.revisionValue = next
  }
}

function decodeOpeningToolContent(): ToolContentRevision {
  let raw: unknown
  try {
    raw = JSON.parse(openingToolContentJson)
  } catch (error) {
    throw new Error(`opening tool content JSON is malformed: ${error instanceof Error ? error.message : String(error)}`)
  }
  return decodeToolContent(raw)
}

export const openingToolContent = new LiveToolContent(decodeOpeningToolContent())
