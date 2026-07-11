import { exploreForm, exploreLabeling } from '../kernel/diagram/canonical/explore'
import { assertClosedGoal, isBlank } from './blank'
import { applyGameStep, currentDiagram, startPuzzle } from './session'
import { GameDomainError, type GameCatalogSource, type PuzzleDefinition, type PuzzleId } from './types'

export type GameCatalog = {
  readonly source: GameCatalogSource
  readonly fingerprint: string
  puzzle(id: PuzzleId): PuzzleDefinition
}

const unique = <T>(values: readonly T[], label: string): void => {
  const seen = new Set<T>()
  for (const value of values) {
    if (seen.has(value)) throw new GameDomainError(`duplicate ${label} '${String(value)}'`)
    seen.add(value)
  }
}

const hash = (text: string): string => {
  let value = 0x811c9dc5
  for (let i = 0; i < text.length; i++) {
    value ^= text.charCodeAt(i)
    value = Math.imul(value, 0x01000193)
  }
  return (value >>> 0).toString(16).padStart(8, '0')
}

const immutableCatalogMutation = (): never => {
  throw new GameDomainError('catalog snapshot is immutable')
}

const ownedSnapshot = <T>(value: T): T => {
  if (value === null || typeof value !== 'object') return value
  if (Array.isArray(value)) {
    return Object.freeze(value.map((entry) => ownedSnapshot(entry))) as T
  }
  if (value instanceof Map) {
    const copy = new Map(
      [...value].map(([key, entry]) => [ownedSnapshot(key), ownedSnapshot(entry)] as const),
    )
    Object.defineProperties(copy, {
      set: { value: immutableCatalogMutation },
      delete: { value: immutableCatalogMutation },
      clear: { value: immutableCatalogMutation },
    })
    return Object.freeze(copy) as T
  }
  const copy = Object.fromEntries(
    Object.entries(value).map(([key, entry]) => [key, ownedSnapshot(entry)]),
  )
  return Object.freeze(copy) as T
}

export function buildCatalog(source: GameCatalogSource): GameCatalog {
  const snapshot = ownedSnapshot(source)
  unique(snapshot.campaigns.map((campaign) => campaign.id), 'campaign id')
  unique(snapshot.puzzles.map((puzzle) => puzzle.id), 'puzzle id')
  const campaigns = new Set(snapshot.campaigns.map((campaign) => campaign.id))
  const byId = new Map(snapshot.puzzles.map((puzzle) => [puzzle.id, puzzle] as const))
  for (const puzzle of snapshot.puzzles) {
    assertClosedGoal(puzzle.goal)
    if (!campaigns.has(puzzle.campaign)) {
      throw new GameDomainError(`puzzle '${puzzle.id}' names unknown campaign '${puzzle.campaign}'`)
    }
    unique(puzzle.prerequisites, `prerequisite of puzzle '${puzzle.id}'`)
    for (const prerequisite of puzzle.prerequisites) {
      if (!byId.has(prerequisite)) {
        throw new GameDomainError(`puzzle '${puzzle.id}' has missing prerequisite '${prerequisite}'`)
      }
    }
  }

  const visiting = new Set<PuzzleId>()
  const visited = new Set<PuzzleId>()
  const order: PuzzleDefinition[] = []
  const visit = (id: PuzzleId): void => {
    if (visiting.has(id)) throw new GameDomainError(`puzzle dependency cycle includes '${id}'`)
    if (visited.has(id)) return
    visiting.add(id)
    const puzzle = byId.get(id)!
    for (const prerequisite of puzzle.prerequisites) visit(prerequisite)
    visiting.delete(id)
    visited.add(id)
    order.push(puzzle)
  }
  for (const puzzle of snapshot.puzzles) visit(puzzle.id)

  const verified = new Set<PuzzleId>()
  const prerequisiteClosure = (puzzle: PuzzleDefinition): ReadonlySet<PuzzleId> => {
    const closure = new Set<PuzzleId>()
    const add = (id: PuzzleId): void => {
      if (closure.has(id)) return
      closure.add(id)
      for (const parent of byId.get(id)!.prerequisites) add(parent)
    }
    for (const id of puzzle.prerequisites) add(id)
    return closure
  }
  for (const puzzle of order) {
    const allowed = prerequisiteClosure(puzzle)
    const authority = {
      context: snapshot.context,
      puzzle(id: PuzzleId) {
        const found = byId.get(id)
        if (found === undefined) throw new GameDomainError(`unknown puzzle '${id}'`)
        return found
      },
      canUseVellum(id: PuzzleId) {
        return allowed.has(id) && verified.has(id) && byId.get(id)?.grantsVellum === true
      },
    }
    let session = startPuzzle(puzzle)
    for (const step of puzzle.witness) session = applyGameStep(session, step, authority).session
    if (!isBlank(currentDiagram(session))) {
      throw new GameDomainError(`puzzle '${puzzle.id}' witness does not reach blank`)
    }
    verified.add(puzzle.id)
  }

  const fingerprintInput = {
    campaigns: [...snapshot.campaigns]
      .map((campaign) => ({ id: campaign.id, title: campaign.title }))
      .sort((a, b) => a.id.localeCompare(b.id)),
    relations: [...snapshot.context.relations]
      .map(([name, relation]) => {
        const canonical = exploreLabeling(relation.diagram, relation.boundary)
        return {
          name,
          boundary: relation.boundary.map((wire) => canonical.wireOrd.get(wire)!),
          diagram: canonical.form,
        }
      })
      .sort((a, b) => a.name.localeCompare(b.name)),
    puzzles: [...snapshot.puzzles]
      .map((puzzle) => ({
        id: puzzle.id, campaign: puzzle.campaign, title: puzzle.title,
        prerequisites: [...puzzle.prerequisites].sort(), grantsVellum: puzzle.grantsVellum,
        goal: exploreForm(puzzle.goal.diagram), witness: puzzle.witness,
      }))
      .sort((a, b) => a.id.localeCompare(b.id)),
  }
  return {
    source: snapshot,
    fingerprint: hash(JSON.stringify(fingerprintInput)),
    puzzle(id: PuzzleId) {
      const puzzle = byId.get(id)
      if (puzzle === undefined) throw new GameDomainError(`unknown puzzle '${id}'`)
      return puzzle
    },
  }
}
