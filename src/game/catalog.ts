import { exploreForm, exploreLabeling } from '../kernel/diagram/canonical/explore'
import { assertClosedGoal, isBlank } from './blank'
import { applyGameStep, currentDiagram, startPuzzle } from './session'
import {
  GameDomainError,
  type CultureDefinition,
  type CultureId,
  type GameCatalogSource,
  type PerformanceId,
  type PuzzleDefinition,
  type PuzzleId,
} from './types'

export type GameCatalog = {
  readonly source: GameCatalogSource
  readonly fingerprint: string
  puzzle(id: PuzzleId): PuzzleDefinition
  culture(id: CultureId): CultureDefinition
}

const unique = <T>(values: readonly T[], label: string): void => {
  const seen = new Set<T>()
  for (const value of values) {
    if (seen.has(value)) throw new GameDomainError(`duplicate ${label} '${String(value)}'`)
    seen.add(value)
  }
}

const nonBlank = (value: string, label: string): void => {
  if (typeof value !== 'string' || value === '' || value.trim() !== value) {
    throw new GameDomainError(`${label} must be a trimmed nonempty string`)
  }
}

const optionalNonBlank = (value: string | undefined, label: string): void => {
  if (value !== undefined) nonBlank(value, label)
}

const sameSet = <T>(left: ReadonlySet<T>, right: ReadonlySet<T>): boolean =>
  left.size === right.size && [...left].every((value) => right.has(value))

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
  unique(snapshot.cultures.map((culture) => culture.id), 'culture id')
  unique(snapshot.cultures.map((culture) => culture.relativeAge), 'culture relative age')
  unique(snapshot.performances.map((performance) => performance.id), 'performance id')
  unique(snapshot.puzzles.map((puzzle) => puzzle.id), 'puzzle id')
  const cultures = new Set(snapshot.cultures.map((culture) => culture.id))
  const cultureById = new Map(snapshot.cultures.map((culture) => [culture.id, culture] as const))
  const performanceById = new Map(
    snapshot.performances.map((performance) => [performance.id, performance] as const),
  )
  const byId = new Map(snapshot.puzzles.map((puzzle) => [puzzle.id, puzzle] as const))

  for (const performance of snapshot.performances) {
    nonBlank(performance.description, `performance '${performance.id}' description`)
    nonBlank(performance.masteryEvidence, `performance '${performance.id}' mastery evidence`)
    if (performance.knowledgePoints.length < 2 || performance.knowledgePoints.length > 5) {
      throw new GameDomainError(
        `performance '${performance.id}' must have two to five knowledge points`,
      )
    }
    unique(
      performance.knowledgePoints.map((point) => point.id),
      `knowledge point of performance '${performance.id}'`,
    )
    for (const point of performance.knowledgePoints) {
      nonBlank(point.id, `knowledge point id of performance '${performance.id}'`)
      nonBlank(point.instruction, `knowledge point '${point.id}' instruction`)
      nonBlank(point.commonError, `knowledge point '${point.id}' common error`)
      nonBlank(point.correction, `knowledge point '${point.id}' correction`)
    }
    unique(performance.prerequisites, `prerequisite of performance '${performance.id}'`)
    unique(performance.remediation, `remediation of performance '${performance.id}'`)
    for (const prerequisite of performance.prerequisites) {
      if (!performanceById.has(prerequisite)) {
        throw new GameDomainError(
          `performance '${performance.id}' has missing performance prerequisite '${prerequisite}'`,
        )
      }
    }
    for (const remediation of performance.remediation) {
      if (!performanceById.has(remediation)) {
        throw new GameDomainError(
          `performance '${performance.id}' has missing remediation performance '${remediation}'`,
        )
      }
    }
  }

  const visitingPerformances = new Set<PerformanceId>()
  const visitedPerformances = new Set<PerformanceId>()
  const visitPerformance = (id: PerformanceId): void => {
    if (visitingPerformances.has(id)) {
      throw new GameDomainError(`performance prerequisite cycle includes '${id}'`)
    }
    if (visitedPerformances.has(id)) return
    visitingPerformances.add(id)
    for (const prerequisite of performanceById.get(id)!.prerequisites) {
      visitPerformance(prerequisite)
    }
    visitingPerformances.delete(id)
    visitedPerformances.add(id)
  }
  for (const performance of snapshot.performances) visitPerformance(performance.id)

  for (const puzzle of snapshot.puzzles) {
    nonBlank(puzzle.name.professional, `puzzle '${puzzle.id}' professional name`)
    optionalNonBlank(puzzle.name.curatorShorthand, `puzzle '${puzzle.id}' curator shorthand`)
    optionalNonBlank(puzzle.name.accession, `puzzle '${puzzle.id}' accession`)
    nonBlank(puzzle.provenance.summary, `puzzle '${puzzle.id}' provenance summary`)
    nonBlank(puzzle.provenance.function, `puzzle '${puzzle.id}' provenance function`)
    optionalNonBlank(puzzle.provenance.findspot, `puzzle '${puzzle.id}' provenance findspot`)
    optionalNonBlank(puzzle.provenance.attributedTo, `puzzle '${puzzle.id}' attribution`)
    for (const beat of puzzle.teacher) {
      nonBlank(beat.text, `puzzle '${puzzle.id}' teacher text`)
    }
    unique(puzzle.misconceptions.map((cue) => cue.id), `misconception of puzzle '${puzzle.id}'`)
    for (const cue of puzzle.misconceptions) {
      nonBlank(cue.id, `misconception id of puzzle '${puzzle.id}'`)
      nonBlank(cue.thought, `misconception '${cue.id}' thought`)
      if (!performanceById.has(cue.performance)) {
        throw new GameDomainError(
          `puzzle '${puzzle.id}' misconception '${cue.id}' names unknown performance '${cue.performance}'`,
        )
      }
    }
    const learningRoles = [
      ['introduces', puzzle.learning.introduces],
      ['practices', puzzle.learning.practices],
      ['retrieves', puzzle.learning.retrieves],
      ['assesses', puzzle.learning.assesses],
    ] as const
    for (const [role, entries] of learningRoles) {
      unique(entries, `${role} learning role of puzzle '${puzzle.id}'`)
      for (const performance of entries) {
        if (!performanceById.has(performance)) {
          throw new GameDomainError(
            `puzzle '${puzzle.id}' ${role} learning role names unknown performance '${performance}'`,
          )
        }
      }
    }
    const declaredRules = new Set(puzzle.learning.rulesUsed)
    const witnessRules = new Set(puzzle.witness.map((step) => step.rule))
    if (!sameSet(declaredRules, witnessRules)) {
      throw new GameDomainError(`puzzle '${puzzle.id}' rulesUsed does not equal witness rules`)
    }
    assertClosedGoal(puzzle.goal)
    if (!cultures.has(puzzle.culture)) {
      throw new GameDomainError(`puzzle '${puzzle.id}' names unknown culture '${puzzle.culture}'`)
    }
    unique(puzzle.prerequisites, `prerequisite of puzzle '${puzzle.id}'`)
    for (const prerequisite of puzzle.prerequisites) {
      if (!byId.has(prerequisite)) {
        throw new GameDomainError(`puzzle '${puzzle.id}' has missing prerequisite '${prerequisite}'`)
      }
    }
  }

  const cultureDependencies = new Map<CultureId, CultureId[]>()
  for (const culture of snapshot.cultures) {
    nonBlank(culture.name, `culture '${culture.id}' name`)
    nonBlank(culture.historicalSummary, `culture '${culture.id}' historical summary`)
    if (!Number.isFinite(culture.relativeAge) || culture.relativeAge < 0) {
      throw new GameDomainError(`culture '${culture.id}' relative age must be nonnegative`)
    }
    if (culture.sealingVocabulary.length === 0) {
      throw new GameDomainError(`culture '${culture.id}' must have sealing vocabulary`)
    }
    unique(culture.sealingVocabulary, `sealing vocabulary of culture '${culture.id}'`)
    for (const term of culture.sealingVocabulary) {
      nonBlank(term, `sealing vocabulary of culture '${culture.id}'`)
    }
    unique(culture.lineage, `lineage identity of culture '${culture.id}'`)
    for (const ancestor of culture.lineage) {
      if (!cultures.has(ancestor)) {
        throw new GameDomainError(`culture '${culture.id}' has missing lineage culture '${ancestor}'`)
      }
    }
    unique(culture.unlocksAfter, `unlock artifact of culture '${culture.id}'`)
    const gateway = byId.get(culture.gateway)
    if (gateway === undefined) {
      throw new GameDomainError(`culture '${culture.id}' has missing gateway '${culture.gateway}'`)
    }
    if (gateway.culture !== culture.id) {
      throw new GameDomainError(
        `culture '${culture.id}' gateway '${culture.gateway}' belongs to culture '${gateway.culture}'`,
      )
    }
    const dependencies: CultureId[] = []
    for (const id of culture.unlocksAfter) {
      const artifact = byId.get(id)
      if (artifact === undefined) {
        throw new GameDomainError(`culture '${culture.id}' has missing unlock artifact '${id}'`)
      }
      if (artifact.culture === culture.id) {
        throw new GameDomainError(`culture '${culture.id}' depends on itself through artifact '${id}'`)
      }
      dependencies.push(artifact.culture)
    }
    cultureDependencies.set(culture.id, dependencies)
  }

  const visitingLineages = new Set<CultureId>()
  const visitedLineages = new Set<CultureId>()
  const visitLineage = (id: CultureId): void => {
    if (visitingLineages.has(id)) {
      throw new GameDomainError(`culture lineage cycle includes '${id}'`)
    }
    if (visitedLineages.has(id)) return
    visitingLineages.add(id)
    for (const ancestor of cultureById.get(id)!.lineage) visitLineage(ancestor)
    visitingLineages.delete(id)
    visitedLineages.add(id)
  }
  for (const culture of snapshot.cultures) visitLineage(culture.id)

  const visitingCultures = new Set<CultureId>()
  const visitedCultures = new Set<CultureId>()
  const visitCulture = (id: CultureId): void => {
    if (visitingCultures.has(id)) {
      throw new GameDomainError(`culture dependency cycle includes '${id}'`)
    }
    if (visitedCultures.has(id)) return
    visitingCultures.add(id)
    for (const dependency of cultureDependencies.get(id)!) visitCulture(dependency)
    visitingCultures.delete(id)
    visitedCultures.add(id)
  }
  for (const culture of snapshot.cultures) visitCulture(culture.id)

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
    cultures: [...snapshot.cultures]
      .map((culture) => ({
        id: culture.id,
        name: culture.name,
        relativeAge: culture.relativeAge,
        historicalSummary: culture.historicalSummary,
        lineage: [...culture.lineage].sort(),
        isolation: culture.isolation,
        sealingVocabulary: culture.sealingVocabulary,
        unlocksAfter: [...culture.unlocksAfter].sort(),
        gateway: culture.gateway,
      }))
      .sort((a, b) => a.id.localeCompare(b.id)),
    performances: [...snapshot.performances]
      .map((performance) => ({
        id: performance.id,
        description: performance.description,
        prerequisites: [...performance.prerequisites].sort(),
        knowledgePoints: performance.knowledgePoints.map((point) => ({
          id: point.id,
          instruction: point.instruction,
          commonError: point.commonError,
          correction: point.correction,
        })),
        masteryEvidence: performance.masteryEvidence,
        remediation: [...performance.remediation].sort(),
      }))
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
        id: puzzle.id,
        culture: puzzle.culture,
        name: {
          professional: puzzle.name.professional,
          curatorShorthand: puzzle.name.curatorShorthand,
          accession: puzzle.name.accession,
        },
        provenance: {
          summary: puzzle.provenance.summary,
          function: puzzle.provenance.function,
          findspot: puzzle.provenance.findspot,
          attributedTo: puzzle.provenance.attributedTo,
        },
        prerequisites: [...puzzle.prerequisites].sort(), grantsVellum: puzzle.grantsVellum,
        goal: exploreForm(puzzle.goal.diagram), witness: puzzle.witness,
        learning: {
          introduces: [...puzzle.learning.introduces].sort(),
          practices: [...puzzle.learning.practices].sort(),
          retrieves: [...puzzle.learning.retrieves].sort(),
          assesses: [...puzzle.learning.assesses].sort(),
          rulesUsed: [...new Set(puzzle.learning.rulesUsed)].sort(),
        },
        teacher: puzzle.teacher.map((beat) => ({ trigger: beat.trigger, text: beat.text })),
        misconceptions: puzzle.misconceptions.map((cue) => ({
          id: cue.id, performance: cue.performance, thought: cue.thought,
        })),
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
    culture(id: CultureId) {
      const culture = cultureById.get(id)
      if (culture === undefined) throw new GameDomainError(`unknown culture '${id}'`)
      return culture
    },
  }
}
