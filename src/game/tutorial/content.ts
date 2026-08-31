import openingTutorialContentJson from '../../../game/content/tutorial.json?raw'
import type { TutorialMilestoneId } from '../tutorial'

export type VisibleTutorialMilestoneId = Exclude<
  TutorialMilestoneId,
  | 'complete-single-double-cut-order'
  | 'complete-irregular-double-cut-a-order'
  | 'complete-irregular-double-cut-b-order'
>

export type TutorialContentDefinition = {
  readonly milestoneId: VisibleTutorialMilestoneId
  readonly text: string
}

export type TutorialContentRevision = {
  readonly definitions: readonly TutorialContentDefinition[]
  definition(milestoneId: string): TutorialContentDefinition
}

const visibleMilestoneIds: readonly VisibleTutorialMilestoneId[] = [
  'move',
  'look',
  'ascend',
  'descend',
  'sprint',
  'select-tree',
  'move-orbit',
  'exit-orbit',
  'spawn-two-sprouts',
  'acquire-double-cut',
  'apply-double-cut',
  'double-cut-explained',
  'acquire-iteration',
  'duplicate-nonblank',
  'iterate-within-tree',
  'complete-blank-order',
]
const visibleMilestoneIdSet = new Set<string>(visibleMilestoneIds)
const decodedRevisions = new WeakSet<TutorialContentRevision>()

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

function decodeDefinition(value: unknown, index: number): TutorialContentDefinition {
  const raw = record(value, `tutorial content ${index}`)
  for (const key of Object.keys(raw)) {
    if (key !== 'milestoneId' && key !== 'text') throw new Error(`tutorial content ${index} has unknown field '${key}'`)
  }
  if (!Object.hasOwn(raw, 'milestoneId') || !Object.hasOwn(raw, 'text')) {
    throw new Error(`tutorial content ${index} must contain milestoneId and text`)
  }
  const milestoneId = nonblankString(raw['milestoneId'], `tutorial content ${index}.milestoneId`)
  if (!visibleMilestoneIdSet.has(milestoneId)) throw new Error(`tutorial content has unknown milestone '${milestoneId}'`)
  return Object.freeze({
    milestoneId: milestoneId as VisibleTutorialMilestoneId,
    text: nonblankString(raw['text'], `tutorial content ${index}.text`),
  })
}

export function decodeTutorialContent(raw: unknown): TutorialContentRevision {
  if (!Array.isArray(raw)) throw new Error('tutorial content must be an array')
  const definitions = raw.map(decodeDefinition)
  const byMilestoneId = new Map<VisibleTutorialMilestoneId, TutorialContentDefinition>()
  for (const definition of definitions) {
    if (byMilestoneId.has(definition.milestoneId)) {
      throw new Error(`tutorial content has duplicate milestone '${definition.milestoneId}'`)
    }
    byMilestoneId.set(definition.milestoneId, definition)
  }
  for (const milestoneId of visibleMilestoneIds) {
    if (!byMilestoneId.has(milestoneId)) throw new Error(`tutorial content is missing milestone '${milestoneId}'`)
  }
  const revision: TutorialContentRevision = Object.freeze({
    definitions: Object.freeze(definitions),
    definition(milestoneId: string): TutorialContentDefinition {
      const definition = byMilestoneId.get(milestoneId as VisibleTutorialMilestoneId)
      if (definition === undefined) throw new Error(`unknown tutorial milestone '${milestoneId}'`)
      return definition
    },
  })
  decodedRevisions.add(revision)
  return revision
}

export class LiveTutorialContent {
  public constructor(private revisionValue: TutorialContentRevision) {
    if (!decodedRevisions.has(revisionValue)) throw new Error('live tutorial content requires a decoded revision')
  }

  public get current(): TutorialContentRevision {
    return this.revisionValue
  }

  public publish(next: TutorialContentRevision): void {
    if (!decodedRevisions.has(next)) throw new Error('live tutorial content requires a decoded revision')
    this.revisionValue = next
  }
}

function decodeOpeningTutorialContent(): TutorialContentRevision {
  let raw: unknown
  try {
    raw = JSON.parse(openingTutorialContentJson)
  } catch (error) {
    throw new Error(`opening tutorial content JSON is malformed: ${error instanceof Error ? error.message : String(error)}`)
  }
  return decodeTutorialContent(raw)
}

export const openingTutorialContent = new LiveTutorialContent(decodeOpeningTutorialContent())
