import { exploreForm, exploreLabeling } from '../kernel/diagram/canonical/explore'
import { stepToJson } from '../kernel/proof/json'
import { artifactTheorem, artifactTheoremContext } from './artifact-theorem'
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
import { meetsUnlockConditions } from './unlock'

export type GameCatalog = {
  readonly source: GameCatalogSource
  readonly fingerprint: string
  puzzleFingerprint(id: PuzzleId): string
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

const stableValue = (value: unknown): unknown => {
  if (Array.isArray(value)) return value.map(stableValue)
  if (value === null || typeof value !== 'object') return value
  return Object.fromEntries(
    Object.entries(value as Record<string, unknown>)
      .sort(([left], [right]) => left.localeCompare(right))
      .map(([key, entry]) => [key, stableValue(entry)]),
  )
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
    unique(
      puzzle.teacher.map((intervention) => intervention.id),
      `teacher intervention id of puzzle '${puzzle.id}'`,
    )
    for (const intervention of puzzle.teacher) {
      nonBlank(intervention.id, `puzzle '${puzzle.id}' teacher intervention id`)
      if (intervention.pages.length === 0) {
        throw new GameDomainError(
          `puzzle '${puzzle.id}' teacher intervention '${intervention.id}' pages must be nonempty`,
        )
      }
      for (const [pageIndex, page] of intervention.pages.entries()) {
        const label = `puzzle '${puzzle.id}' teacher intervention '${intervention.id}' page ${pageIndex}`
        nonBlank(page, label)
        if (page.includes('\n') || page.includes('\r')) {
          throw new GameDomainError(`${label} must be a single paragraph`)
        }
      }
      if (
        intervention.performance !== undefined
        && !performanceById.has(intervention.performance)
      ) {
        throw new GameDomainError(
          `puzzle '${puzzle.id}' teacher intervention '${intervention.id}' names unknown performance '${intervention.performance}'`,
        )
      }
      const trigger = intervention.trigger
      switch (trigger.kind) {
        case 'opening':
          break
        case 'completion':
          if (intervention.pages.length !== 1) {
            throw new GameDomainError(
              `puzzle '${puzzle.id}' completion teacher intervention '${intervention.id}' must have one page`,
            )
          }
          break
        case 'recognizedUnwinnable':
          if (intervention.recovery !== 'timeline') {
            throw new GameDomainError(
              `puzzle '${puzzle.id}' teacher intervention '${intervention.id}' unwinnable commentary must recover through the timeline`,
            )
          }
          if (trigger.demonstration.length === 0) {
            throw new GameDomainError(
              `puzzle '${puzzle.id}' teacher intervention '${intervention.id}' unwinnable-state demonstration must be nonempty`,
            )
          }
          assertClosedGoal(trigger.state)
          if (isBlank(trigger.state.diagram)) {
            throw new GameDomainError(
              `puzzle '${puzzle.id}' teacher intervention '${intervention.id}' unwinnable state must not be canonical blank; completion owns that event`,
            )
          }
          break
        default: {
          const exhaustive: never = trigger
          throw new GameDomainError(`unknown teacher trigger '${String(exhaustive)}'`)
        }
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

  const reachable = new Set<PuzzleId>()
  while (true) {
    const available = snapshot.puzzles.filter((puzzle) =>
      !reachable.has(puzzle.id)
      && meetsUnlockConditions(cultureById.get(puzzle.culture)!, puzzle, reachable),
    )
    if (available.length === 0) break
    for (const puzzle of available) reachable.add(puzzle.id)
  }
  if (reachable.size !== snapshot.puzzles.length) {
    const unreachable = snapshot.puzzles.filter((puzzle) => !reachable.has(puzzle.id))
    const unreachableCultures = [...new Set(unreachable.map((puzzle) => puzzle.culture))]
    throw new GameDomainError(
      `unreachable puzzles ${unreachable.map((puzzle) => `'${puzzle.id}'`).join(', ')}`
      + ` in cultures ${unreachableCultures.map((id) => `'${id}'`).join(', ')}`,
    )
  }

  const verified = new Set<PuzzleId>()
  const prerequisiteClosure = (puzzle: PuzzleDefinition): Set<PuzzleId> => {
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
    const completedPrerequisites = prerequisiteClosure(puzzle)
    for (const id of completedPrerequisites) {
      if (!verified.has(id)) {
        throw new GameDomainError(
          `puzzle '${puzzle.id}' prerequisite artifact '${id}' was not verified before use`,
        )
      }
    }
    const context = artifactTheoremContext(
      snapshot.puzzles,
      completedPrerequisites,
      snapshot.context,
    )
    const authority = { context }
    let session = startPuzzle(puzzle)
    for (const step of puzzle.witness) session = applyGameStep(session, step, authority).session
    if (!isBlank(currentDiagram(session))) {
      throw new GameDomainError(`puzzle '${puzzle.id}' witness does not reach blank`)
    }
    for (const intervention of puzzle.teacher) {
      if (intervention.trigger.kind !== 'recognizedUnwinnable') continue
      let demonstration = startPuzzle(puzzle)
      for (const step of intervention.trigger.demonstration) {
        demonstration = applyGameStep(demonstration, step, authority).session
      }
      const reached = exploreForm(currentDiagram(demonstration))
      const declared = exploreForm(intervention.trigger.state.diagram)
      if (reached !== declared) {
        throw new GameDomainError(
          `puzzle '${puzzle.id}' teacher intervention '${intervention.id}' demonstration does not reach its declared unwinnable state`,
        )
      }
    }
    artifactTheorem(puzzle, context)
    verified.add(puzzle.id)
  }

  const relationLogic = [...snapshot.context.relations]
    .map(([name, relation]) => {
      const canonical = exploreLabeling(relation.diagram, relation.boundary)
      return {
        name,
        boundary: relation.boundary.map((wire) => canonical.wireOrd.get(wire)!),
        diagram: canonical.form,
      }
    })
    .sort((left, right) => left.name.localeCompare(right.name))
  const logicalFingerprints = new Map(snapshot.puzzles.map((puzzle) => {
    const logicalInput = {
      id: puzzle.id,
      goal: exploreForm(puzzle.goal.diagram),
      prerequisites: [...puzzle.prerequisites].sort(),
      relations: relationLogic,
      witness: puzzle.witness.map((step) => stableValue(stepToJson(step))),
    }
    return [puzzle.id, hash(JSON.stringify(logicalInput))] as const
  }))
  const fingerprintInput = [...logicalFingerprints]
    .sort(([left], [right]) => left.localeCompare(right))
  return {
    source: snapshot,
    fingerprint: hash(JSON.stringify(fingerprintInput)),
    puzzleFingerprint(id: PuzzleId) {
      const fingerprint = logicalFingerprints.get(id)
      if (fingerprint === undefined) throw new GameDomainError(`unknown puzzle '${id}'`)
      return fingerprint
    },
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
