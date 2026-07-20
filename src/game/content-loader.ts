import { exploreForm, exploreLabeling } from '../kernel/diagram/canonical/explore'
import { mkDiagramWithBoundary, type DiagramWithBoundary } from '../kernel/diagram/boundary'
import { diagramFromJson } from '../kernel/diagram/json'
import type { Diagram } from '../kernel/diagram/diagram'
import { isBlank } from './blank'
import {
  GameDomainError,
  cultureId,
  puzzleId,
  type ArtifactDefinition,
  type CatalogCultureDefinition,
  type CultureId,
  type ProgressionCultureDefinition,
  type PuzzlePlacement,
  type GuidanceDefinition,
  type GuidanceIntervention,
  type PuzzleDefinition,
  type PuzzleId,
} from './types'

export type GameContentFiles = Readonly<Record<string, unknown>>

export type ContentCulture = CatalogCultureDefinition & ProgressionCultureDefinition

export type PortableGameCatalog = {
  readonly fingerprint: string
  readonly puzzleIds: readonly PuzzleId[]
  readonly cultureIds: readonly CultureId[]
  readonly context: { readonly relations: ReadonlyMap<string, DiagramWithBoundary> }
  puzzleFingerprint(id: PuzzleId): string
  puzzle(id: PuzzleId): PuzzleDefinition
  placement(id: PuzzleId): PuzzlePlacement
  artifact(id: PuzzleId): ArtifactDefinition
  guidance(id: PuzzleId): GuidanceDefinition
  culture(id: CultureId): ContentCulture
  puzzlesInCulture(id: CultureId): readonly PuzzleId[]
}

type JsonRecord = Record<string, unknown>

const record = (value: unknown, label: string): JsonRecord => {
  if (typeof value !== 'object' || value === null || Array.isArray(value)) {
    throw new GameDomainError(`${label} must be an object`)
  }
  return value as JsonRecord
}

const only = (value: JsonRecord, allowed: readonly string[], label: string): void => {
  for (const key of Object.keys(value)) {
    if (!allowed.includes(key)) throw new GameDomainError(`${label} has unknown field '${key}'`)
  }
}

const array = (value: unknown, label: string): unknown[] => {
  if (!Array.isArray(value)) throw new GameDomainError(`${label} must be an array`)
  return value
}

const string = (value: unknown, label: string): string => {
  if (typeof value !== 'string' || value.length === 0 || value.trim() !== value) {
    throw new GameDomainError(`${label} must be a trimmed nonempty string`)
  }
  return value
}

const optionalString = (value: unknown, label: string): string | undefined =>
  value === undefined ? undefined : string(value, label)

const integer = (value: unknown, label: string): number => {
  if (!Number.isSafeInteger(value) || (value as number) < 0) {
    throw new GameDomainError(`${label} must be a nonnegative integer`)
  }
  return value as number
}

const strings = (value: unknown, label: string): string[] =>
  array(value, label).map((entry, index) => string(entry, `${label}[${index}]`))

const unique = <T>(values: readonly T[], label: string): void => {
  const seen = new Set<T>()
  for (const value of values) {
    if (seen.has(value)) throw new GameDomainError(`duplicate ${label} '${String(value)}'`)
    seen.add(value)
  }
}

const file = (files: GameContentFiles, path: string): unknown => {
  if (!Object.hasOwn(files, path)) throw new GameDomainError(`content manifest names missing file '${path}'`)
  return files[path]
}

const ownedSnapshot = <T>(value: T): T => {
  if (value === null || typeof value !== 'object') return value
  if (Array.isArray(value)) return Object.freeze(value.map(ownedSnapshot)) as T
  if (value instanceof Map) {
    const copy = new Map([...value].map(([key, entry]) => [ownedSnapshot(key), ownedSnapshot(entry)]))
    Object.defineProperties(copy, {
      set: { value: () => { throw new GameDomainError('catalog snapshot is immutable') } },
      delete: { value: () => { throw new GameDomainError('catalog snapshot is immutable') } },
      clear: { value: () => { throw new GameDomainError('catalog snapshot is immutable') } },
    })
    return Object.freeze(copy) as T
  }
  return Object.freeze(Object.fromEntries(
    Object.entries(value as JsonRecord).map(([key, entry]) => [key, ownedSnapshot(entry)]),
  )) as T
}

const parseProgression = (value: unknown): {
  cultures: ProgressionCultureDefinition[]
  placements: Omit<PuzzlePlacement, 'culture'>[]
} => {
  const raw = record(value, 'progression')
  only(raw, ['cultures', 'placements'], 'progression')
  const cultures = array(raw.cultures, 'progression cultures').map((entry, index) => {
    const culture = record(entry, `progression culture ${index}`)
    only(culture, ['id', 'order', 'unlocksAfter', 'gateway', 'puzzles'], `progression culture ${index}`)
    const id = cultureId(string(culture.id, `progression culture ${index} id`))
    return {
      id,
      order: integer(culture.order, `progression culture '${id}' order`),
      unlocksAfter: strings(culture.unlocksAfter, `progression culture '${id}' unlocksAfter`).map(puzzleId),
      gateway: puzzleId(string(culture.gateway, `progression culture '${id}' gateway`)),
      puzzles: strings(culture.puzzles, `progression culture '${id}' puzzles`).map(puzzleId),
    }
  })
  const placements = array(raw.placements, 'progression placements').map((entry, index) => {
    const placement = record(entry, `progression placement ${index}`)
    only(placement, ['puzzle', 'prerequisites'], `progression placement ${index}`)
    const id = puzzleId(string(placement.puzzle, `progression placement ${index} puzzle`))
    return {
      puzzle: id,
      prerequisites: strings(placement.prerequisites, `progression placement '${id}' prerequisites`).map(puzzleId),
    }
  })
  return { cultures, placements }
}

const parseCatalog = (value: unknown): {
  cultures: CatalogCultureDefinition[]
  artifacts: ArtifactDefinition[]
} => {
  const raw = record(value, 'catalog')
  only(raw, ['cultures', 'artifacts'], 'catalog')
  const cultures = array(raw.cultures, 'catalog cultures').map((entry, index) => {
    const culture = record(entry, `catalog culture ${index}`)
    only(culture, ['id', 'name', 'shortName', 'relativeAge', 'historicalSummary', 'lineage', 'isolation', 'sealingVocabulary'], `catalog culture ${index}`)
    const isolation = string(culture.isolation, `catalog culture ${index} isolation`)
    if (isolation !== 'connected' && isolation !== 'isolated' && isolation !== 'uncertain') {
      throw new GameDomainError(`catalog culture ${index} isolation is invalid`)
    }
    return {
      id: cultureId(string(culture.id, `catalog culture ${index} id`)),
      name: string(culture.name, `catalog culture ${index} name`),
      shortName: string(culture.shortName, `catalog culture ${index} shortName`),
      relativeAge: integer(culture.relativeAge, `catalog culture ${index} relativeAge`),
      historicalSummary: string(culture.historicalSummary, `catalog culture ${index} historicalSummary`),
      lineage: strings(culture.lineage, `catalog culture ${index} lineage`).map(cultureId),
      isolation: isolation as CatalogCultureDefinition['isolation'],
      sealingVocabulary: strings(culture.sealingVocabulary, `catalog culture ${index} sealingVocabulary`),
    }
  })
  const artifacts = array(raw.artifacts, 'catalog artifacts').map((entry, index) => {
    const artifact = record(entry, `catalog artifact ${index}`)
    only(artifact, ['puzzle', 'name', 'provenance'], `catalog artifact ${index}`)
    const id = puzzleId(string(artifact.puzzle, `catalog artifact ${index} puzzle`))
    const name = record(artifact.name, `catalog artifact '${id}' name`)
    only(name, ['professional', 'curatorShorthand', 'accession'], `catalog artifact '${id}' name`)
    const provenance = record(artifact.provenance, `catalog artifact '${id}' provenance`)
    only(provenance, ['summary', 'function', 'findspot', 'attributedTo'], `catalog artifact '${id}' provenance`)
    const curatorShorthand = optionalString(name.curatorShorthand, `catalog artifact '${id}' curatorShorthand`)
    const accession = optionalString(name.accession, `catalog artifact '${id}' accession`)
    const findspot = optionalString(provenance.findspot, `catalog artifact '${id}' findspot`)
    const attributedTo = optionalString(provenance.attributedTo, `catalog artifact '${id}' attributedTo`)
    return {
      puzzle: id,
      name: {
        professional: string(name.professional, `catalog artifact '${id}' professional name`),
        ...(curatorShorthand === undefined ? {} : { curatorShorthand }),
        ...(accession === undefined ? {} : { accession }),
      },
      provenance: {
        summary: string(provenance.summary, `catalog artifact '${id}' provenance summary`),
        function: string(provenance.function, `catalog artifact '${id}' provenance function`),
        ...(findspot === undefined ? {} : { findspot }),
        ...(attributedTo === undefined ? {} : { attributedTo }),
      },
    }
  })
  return { cultures, artifacts }
}

const parseGuidance = (value: unknown): GuidanceDefinition[] => {
  const raw = record(value, 'guidance')
  only(raw, ['puzzles'], 'guidance')
  return array(raw.puzzles, 'guidance puzzles').map((entry, index) => {
    const puzzleGuidance = record(entry, `guidance puzzle ${index}`)
    only(puzzleGuidance, ['puzzle', 'interventions'], `guidance puzzle ${index}`)
    const puzzle = puzzleId(string(puzzleGuidance.puzzle, `guidance puzzle ${index} puzzle`))
    const interventions = array(puzzleGuidance.interventions, `guidance '${puzzle}' interventions`).map((item, interventionIndex): GuidanceIntervention => {
      const intervention = record(item, `guidance '${puzzle}' intervention ${interventionIndex}`)
      only(intervention, ['id', 'trigger', 'repeat', 'pages', 'recovery'], `guidance '${puzzle}' intervention ${interventionIndex}`)
      const id = string(intervention.id, `guidance '${puzzle}' intervention id`)
      const repeat = string(intervention.repeat, `guidance '${puzzle}' intervention '${id}' repeat`)
      if (repeat !== 'once' && repeat !== 'repeatable') throw new GameDomainError(`guidance '${puzzle}' intervention '${id}' repeat is invalid`)
      const trigger = record(intervention.trigger, `guidance '${puzzle}' intervention '${id}' trigger`)
      const kind = string(trigger.kind, `guidance '${puzzle}' intervention '${id}' trigger kind`)
      const pages = strings(intervention.pages, `guidance '${puzzle}' intervention '${id}' pages`)
      if (pages.length === 0) throw new GameDomainError(`guidance '${puzzle}' intervention '${id}' pages must be nonempty`)
      for (const page of pages) if (page.includes('\n') || page.includes('\r')) throw new GameDomainError(`guidance '${puzzle}' intervention '${id}' pages must be single paragraphs`)
      const base = { id, pages, repeat } as const
      if (kind === 'opening' || kind === 'completion') {
        only(trigger, ['kind'], `guidance '${puzzle}' intervention '${id}' trigger`)
        if (intervention.recovery !== undefined) throw new GameDomainError(`guidance '${puzzle}' intervention '${id}' recovery is only valid for recognizedUnwinnable`)
        if (kind === 'completion' && pages.length !== 1) throw new GameDomainError(`guidance '${puzzle}' completion intervention '${id}' must have one page`)
        return { ...base, trigger: { kind } }
      }
      if (kind === 'recognizedUnwinnable') {
        only(trigger, ['kind', 'state'], `guidance '${puzzle}' intervention '${id}' trigger`)
        if (intervention.recovery !== 'timeline') throw new GameDomainError(`guidance '${puzzle}' intervention '${id}' must recover through the timeline`)
        const state = mkDiagramWithBoundary(diagramFromJson(trigger.state), [])
        if (isBlank(state.diagram)) throw new GameDomainError(`guidance '${puzzle}' intervention '${id}' recognized state cannot be canonical blank`)
        return { ...base, trigger: { kind, state }, recovery: 'timeline' }
      }
      throw new GameDomainError(`guidance '${puzzle}' intervention '${id}' trigger kind is invalid`)
    })
    return { puzzle, interventions }
  })
}

const referencedDefinitions = (diagram: Diagram): string[] =>
  Object.values(diagram.nodes).flatMap((node) => node.kind === 'ref' ? [node.defId] : [])

export function loadGameContent(files: GameContentFiles): PortableGameCatalog {
  const manifest = record(file(files, 'manifest.json'), 'content manifest')
  only(manifest, ['format', 'version', 'puzzles', 'definitions', 'progression', 'coverage', 'catalog', 'guidance'], 'content manifest')
  if (manifest.format !== 'cursebreaker-content') throw new GameDomainError("content manifest format must be 'cursebreaker-content'")
  if (manifest.version !== 2) throw new GameDomainError('content manifest version must be 2')
  const puzzlePaths = strings(manifest.puzzles, 'content manifest puzzles')
  const definitionPaths = strings(manifest.definitions, 'content manifest definitions')
  unique(puzzlePaths, 'puzzle path')
  unique(definitionPaths, 'definition path')
  const progressionPath = string(manifest.progression, 'content manifest progression')
  string(manifest.coverage, 'content manifest coverage')
  const catalogPath = string(manifest.catalog, 'content manifest catalog')
  const guidancePath = string(manifest.guidance, 'content manifest guidance')

  const puzzles = puzzlePaths.map((path): PuzzleDefinition => {
    const raw = record(file(files, path), `puzzle file '${path}'`)
    only(raw, ['id', 'diagram'], `puzzle file '${path}'`)
    return { id: puzzleId(string(raw.id, `puzzle file '${path}' id`)), diagram: diagramFromJson(raw.diagram) }
  })
  const definitions = definitionPaths.map((path) => {
    const raw = record(file(files, path), `definition file '${path}'`)
    only(raw, ['id', 'diagram', 'boundary'], `definition file '${path}'`)
    const id = string(raw.id, `definition file '${path}' id`)
    return [id, mkDiagramWithBoundary(diagramFromJson(raw.diagram), strings(raw.boundary, `definition '${id}' boundary`))] as const
  })
  const progression = parseProgression(file(files, progressionPath))
  const catalogData = parseCatalog(file(files, catalogPath))
  const guidanceData = parseGuidance(file(files, guidancePath))

  unique(puzzles.map(({ id }) => id), 'puzzle id')
  unique(definitions.map(([id]) => id), 'definition id')
  unique(progression.cultures.map(({ id }) => id), 'progression culture id')
  unique(progression.cultures.map(({ order }) => order), 'progression culture order')
  unique(progression.placements.map(({ puzzle }) => puzzle), 'progression placement')
  unique(catalogData.cultures.map(({ id }) => id), 'catalog culture id')
  unique(catalogData.artifacts.map(({ puzzle }) => puzzle), 'catalog artifact')
  unique(guidanceData.map(({ puzzle }) => puzzle), 'guidance puzzle')

  const puzzleById = new Map(puzzles.map((entry) => [entry.id, entry] as const))
  const definitionById = new Map(definitions)
  const progressionCultureById = new Map(progression.cultures.map((entry) => [entry.id, entry] as const))
  const catalogCultureById = new Map(catalogData.cultures.map((entry) => [entry.id, entry] as const))
  const artifactById = new Map(catalogData.artifacts.map((entry) => [entry.puzzle, entry] as const))
  const guidanceById = new Map(guidanceData.map((entry) => [entry.puzzle, entry] as const))

  const assertAcyclic = <T>(
    ids: readonly T[],
    dependencies: (id: T) => readonly T[],
    label: string,
  ): void => {
    const visiting = new Set<T>()
    const visited = new Set<T>()
    const visit = (id: T): void => {
      if (visiting.has(id)) throw new GameDomainError(`${label} cycle includes '${String(id)}'`)
      if (visited.has(id)) return
      visiting.add(id)
      for (const dependency of dependencies(id)) visit(dependency)
      visiting.delete(id)
      visited.add(id)
    }
    for (const id of ids) visit(id)
  }

  if (progressionCultureById.size !== catalogCultureById.size || [...progressionCultureById].some(([id]) => !catalogCultureById.has(id))) {
    throw new GameDomainError('progression and catalog cultures must match exactly')
  }
  const owner = new Map<PuzzleId, CultureId>()
  for (const culture of progression.cultures) {
    unique(culture.puzzles, `puzzle order of culture '${culture.id}'`)
    for (const id of culture.puzzles) {
      if (!puzzleById.has(id)) throw new GameDomainError(`culture '${culture.id}' names unknown puzzle '${id}'`)
      if (owner.has(id)) throw new GameDomainError(`puzzle '${id}' belongs to multiple cultures`)
      owner.set(id, culture.id)
    }
    if (!culture.puzzles.includes(culture.gateway)) throw new GameDomainError(`culture '${culture.id}' gateway '${culture.gateway}' is not in its puzzle order`)
  }
  const placements = progression.placements.map((entry): PuzzlePlacement => {
    const culture = owner.get(entry.puzzle)
    if (culture === undefined) throw new GameDomainError(`puzzle '${entry.puzzle}' has no progression culture`)
    return { ...entry, culture }
  })
  const placementById = new Map(placements.map((entry) => [entry.puzzle, entry] as const))
  for (const puzzle of puzzles) {
    if (!placementById.has(puzzle.id)) throw new GameDomainError(`puzzle '${puzzle.id}' has no progression placement`)
    if (!artifactById.has(puzzle.id)) throw new GameDomainError(`puzzle '${puzzle.id}' has no catalog artifact`)
    if (!owner.has(puzzle.id)) throw new GameDomainError(`puzzle '${puzzle.id}' has no progression culture`)
    for (const definition of referencedDefinitions(puzzle.diagram)) if (!definitionById.has(definition)) throw new GameDomainError(`puzzle '${puzzle.id}' references unknown definition '${definition}'`)
  }
  for (const id of [...placementById.keys(), ...artifactById.keys(), ...guidanceById.keys()]) {
    if (!puzzleById.has(id)) throw new GameDomainError(`content overlay names unknown puzzle '${id}'`)
  }
  for (const placement of placements) {
    unique(placement.prerequisites, `prerequisite of puzzle '${placement.puzzle}'`)
    for (const prerequisite of placement.prerequisites) if (!puzzleById.has(prerequisite)) throw new GameDomainError(`puzzle '${placement.puzzle}' has missing prerequisite '${prerequisite}'`)
  }
  for (const entry of guidanceData) {
    unique(entry.interventions.map(({ id }) => id), `guidance intervention of puzzle '${entry.puzzle}'`)
  }

  const visiting = new Set<PuzzleId>()
  const visited = new Set<PuzzleId>()
  const visit = (id: PuzzleId): void => {
    if (visiting.has(id)) throw new GameDomainError(`puzzle dependency cycle includes '${id}'`)
    if (visited.has(id)) return
    visiting.add(id)
    for (const prerequisite of placementById.get(id)!.prerequisites) visit(prerequisite)
    visiting.delete(id)
    visited.add(id)
  }
  for (const puzzle of puzzles) visit(puzzle.id)

  const combinedCultures = progression.cultures
    .sort((left, right) => left.order - right.order)
    .map((entry): ContentCulture => ({ ...catalogCultureById.get(entry.id)!, ...entry }))
  const cultureById = new Map(combinedCultures.map((entry) => [entry.id, entry] as const))
  for (const culture of combinedCultures) {
    for (const ancestor of culture.lineage) if (!cultureById.has(ancestor)) throw new GameDomainError(`culture '${culture.id}' names unknown lineage culture '${ancestor}'`)
    for (const unlock of culture.unlocksAfter) if (!puzzleById.has(unlock)) throw new GameDomainError(`culture '${culture.id}' names unknown unlock puzzle '${unlock}'`)
  }
  assertAcyclic(
    combinedCultures.map(({ id }) => id),
    (id) => cultureById.get(id)!.lineage,
    'culture lineage',
  )
  assertAcyclic(
    combinedCultures.map(({ id }) => id),
    (id) => [...new Set(cultureById.get(id)!.unlocksAfter.map((puzzle) => owner.get(puzzle)!))],
    'culture unlock dependency',
  )
  const reachable = new Set<PuzzleId>()
  while (true) {
    const available = placements.filter((placement) => {
      if (reachable.has(placement.puzzle)) return false
      const culture = cultureById.get(placement.culture)!
      return culture.unlocksAfter.every((id) => reachable.has(id)) && placement.prerequisites.every((id) => reachable.has(id))
    })
    if (available.length === 0) break
    for (const placement of available) reachable.add(placement.puzzle)
  }
  if (reachable.size !== puzzles.length) throw new GameDomainError('progression contains unreachable puzzles')

  const replaceDefinitionNames = (diagram: Diagram, resolveDefinition: (id: string) => string): Diagram => ({
    ...diagram,
    nodes: Object.fromEntries(Object.entries(diagram.nodes).map(([id, node]) => [
      id,
      node.kind === 'ref' ? { ...node, defId: resolveDefinition(node.defId) } : node,
    ])),
  })
  const definitionSemantics = new Map<string, string>()
  const visitingDefinitions = new Set<string>()
  const definitionSemanticForm = (id: string): string => {
    const known = definitionSemantics.get(id)
    if (known !== undefined) return known
    if (visitingDefinitions.has(id)) throw new GameDomainError(`definition dependency cycle includes '${id}'`)
    const definition = definitionById.get(id)
    if (definition === undefined) throw new GameDomainError(`unknown definition '${id}'`)
    visitingDefinitions.add(id)
    const normalized = replaceDefinitionNames(definition.diagram, definitionSemanticForm)
    const labeling = exploreLabeling(normalized, definition.boundary)
    const form = JSON.stringify({
      diagram: labeling.form,
      boundary: definition.boundary.map((wire) => labeling.wireOrd.get(wire)!),
    })
    visitingDefinitions.delete(id)
    definitionSemantics.set(id, form)
    return form
  }
  for (const id of definitionById.keys()) definitionSemanticForm(id)
  const logicalFingerprints = new Map(puzzles.map((puzzle) => [
    puzzle.id,
    JSON.stringify({
      diagram: exploreForm(replaceDefinitionNames(puzzle.diagram, definitionSemanticForm)),
    }),
  ] as const))

  const emptyGuidance = (id: PuzzleId): GuidanceDefinition => ({ puzzle: id, interventions: [] })
  const snapshot = ownedSnapshot({
    puzzleIds: puzzles.map(({ id }) => id),
    cultureIds: combinedCultures.map(({ id }) => id),
    puzzles,
    placements,
    artifacts: catalogData.artifacts,
    guidance: guidanceData,
    cultures: combinedCultures,
    relations: definitionById,
  })
  const snapPuzzleById = new Map(snapshot.puzzles.map((entry) => [entry.id, entry] as const))
  const snapPlacementById = new Map(snapshot.placements.map((entry) => [entry.puzzle, entry] as const))
  const snapArtifactById = new Map(snapshot.artifacts.map((entry) => [entry.puzzle, entry] as const))
  const snapGuidanceById = new Map(snapshot.guidance.map((entry) => [entry.puzzle, entry] as const))
  const snapCultureById = new Map(snapshot.cultures.map((entry) => [entry.id, entry] as const))
  const unknown = (kind: string, id: string): never => { throw new GameDomainError(`unknown ${kind} '${id}'`) }
  return {
    fingerprint: JSON.stringify([...logicalFingerprints].sort(([left], [right]) => left.localeCompare(right))),
    puzzleIds: snapshot.puzzleIds,
    cultureIds: snapshot.cultureIds,
    context: ownedSnapshot({ relations: snapshot.relations }),
    puzzleFingerprint: (id) => logicalFingerprints.get(id) ?? unknown('puzzle', id),
    puzzle: (id) => snapPuzzleById.get(id) ?? unknown('puzzle', id),
    placement: (id) => snapPlacementById.get(id) ?? unknown('puzzle placement', id),
    artifact: (id) => snapArtifactById.get(id) ?? unknown('artifact', id),
    guidance: (id) => snapGuidanceById.get(id) ?? ownedSnapshot(emptyGuidance(id)),
    culture: (id) => snapCultureById.get(id) ?? unknown('culture', id),
    puzzlesInCulture: (id) => snapCultureById.get(id)?.puzzles ?? unknown('culture', id),
  }
}
