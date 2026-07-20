import Ajv2020, { type AnySchema, type ValidateFunction } from 'ajv/dist/2020.js'
import { readFileSync, readdirSync } from 'node:fs'
import { resolve } from 'node:path'
import { pathToFileURL } from 'node:url'
import { exploreForm } from '../src/kernel/diagram/canonical/explore'
import type { Diagram, RegionId } from '../src/kernel/diagram/diagram'
import { cutDepth } from '../src/kernel/diagram/regions'
import { stepFromJson } from '../src/kernel/proof/json'
import { artifactTheoremContext } from '../src/game/artifact-theorem'
import { isBlank } from '../src/game/blank'
import { loadGameContent, type GameContentFiles } from '../src/game/catalog'
import {
  analyzeSeyricPropositionalShape,
  analyzeSeyricStart,
  auditSeyricWitness,
} from '../src/game/content/seyric-authority'
import { applyGameSteps, currentDiagram, startPuzzle } from '../src/game/session'
import {
  GameDomainError,
  cultureId,
  puzzleId,
  type CultureId,
  type GameStep,
  type PuzzleId,
} from '../src/game/types'
export { analyzeSeyricPropositionalShape, analyzeSeyricStart, auditSeyricWitness }

type JsonRecord = Record<string, unknown>
type ValidationEvidence = {
  puzzle: PuzzleId
  solution: readonly GameStep[]
  availableArtifacts: readonly PuzzleId[]
  expectedRules: readonly string[]
  recognizedStates: readonly { intervention: string; demonstration: readonly GameStep[] }[]
}
type CoverageObligation = {
  id: string
  family: string
  distinction: string
  stoppingRule: string
}
type CoverageRow = {
  puzzle: PuzzleId
  obligations: readonly string[]
  visibleSituation: string
  defeats: string
  experientialNeighbors: readonly PuzzleId[]
  immediateComplementPattern?: string
}

export type ContentValidationReceipt = {
  readonly puzzles: number
  readonly solutions: number
  readonly recognizedStates: number
}

const directChildRegions = (diagram: Diagram, parent: RegionId): RegionId[] =>
  Object.entries(diagram.regions)
    .filter(([, region]) => region.kind !== 'sheet' && region.parent === parent)
    .map(([id]) => id)

const directNodeCount = (diagram: Diagram, region: RegionId): number =>
  Object.values(diagram.nodes).filter((node) => node.region === region).length

const isEmptyCut = (diagram: Diagram, region: RegionId): boolean =>
  diagram.regions[region]?.kind === 'cut'
  && directChildRegions(diagram, region).length === 0
  && directNodeCount(diagram, region) === 0

export function findEmptyCutShortcutHosts(diagram: Diagram): readonly RegionId[] {
  const hosts: RegionId[] = []
  for (const id of Object.keys(diagram.regions)) {
    if (cutDepth(diagram, id) % 2 === 0) continue
    const children = directChildRegions(diagram, id)
    const emptyCuts = children.filter((child) => isEmptyCut(diagram, child))
    if (emptyCuts.length === 0) continue
    const competingRegions = children.filter((child) => !emptyCuts.includes(child))
    if (competingRegions.length > 0 || directNodeCount(diagram, id) > 0) hosts.push(id)
  }
  return hosts
}

const parseJson = (path: string): unknown => JSON.parse(readFileSync(path, 'utf8')) as unknown
const parseSchema = (path: string): AnySchema => parseJson(path) as AnySchema

const record = (value: unknown, label: string): JsonRecord => {
  if (typeof value !== 'object' || value === null || Array.isArray(value)) {
    throw new GameDomainError(`${label} must be an object`)
  }
  return value as JsonRecord
}

const strings = (value: unknown, label: string): string[] => {
  if (!Array.isArray(value) || !value.every((entry) => typeof entry === 'string')) {
    throw new GameDomainError(`${label} must be an array of strings`)
  }
  return value as string[]
}

const nonempty = (value: unknown, label: string): string => {
  if (typeof value !== 'string' || value.trim().length === 0) {
    throw new GameDomainError(`${label} must be a nonempty string`)
  }
  return value
}

const formatErrors = (validator: ValidateFunction): string =>
  validator.errors?.map((error) => `${error.instancePath || '/'} ${error.message ?? 'is invalid'}`).join('; ')
  ?? 'unknown schema error'

const requireSchema = (validator: ValidateFunction, value: unknown, path: string): void => {
  if (!validator(value)) throw new GameDomainError(`${path}: ${formatErrors(validator)}`)
}

const parseEvidence = (value: unknown, path: string): ValidationEvidence => {
  const raw = record(value, path)
  const solution = Array.isArray(raw.solution)
    ? raw.solution.map((step, index) => {
        try { return stepFromJson(step) } catch (error) {
          throw new GameDomainError(`${path} solution step ${index}: ${error instanceof Error ? error.message : String(error)}`)
        }
      })
    : (() => { throw new GameDomainError(`${path} solution must be an array`) })()
  if (!Array.isArray(raw.recognizedStates)) throw new GameDomainError(`${path} recognizedStates must be an array`)
  const recognizedStates = raw.recognizedStates.map((entry, index) => {
    const state = record(entry, `${path} recognized state ${index}`)
    const intervention = typeof state.intervention === 'string'
      ? state.intervention
      : (() => { throw new GameDomainError(`${path} recognized state ${index} intervention must be a string`) })()
    if (!Array.isArray(state.demonstration)) throw new GameDomainError(`${path} recognized state '${intervention}' demonstration must be an array`)
    return {
      intervention,
      demonstration: state.demonstration.map((step, stepIndex) => {
        try { return stepFromJson(step) } catch (error) {
          throw new GameDomainError(`${path} recognized state '${intervention}' step ${stepIndex}: ${error instanceof Error ? error.message : String(error)}`)
        }
      }),
    }
  })
  return {
    puzzle: puzzleId(typeof raw.puzzle === 'string' ? raw.puzzle : ''),
    solution,
    availableArtifacts: strings(raw.availableArtifacts, `${path} availableArtifacts`).map(puzzleId),
    expectedRules: strings(raw.expectedRules, `${path} expectedRules`),
    recognizedStates,
  }
}

const parseCoverage = (value: unknown, path: string): {
  obligations: CoverageObligation[]
  puzzles: CoverageRow[]
} => {
  const raw = record(value, path)
  if (!Array.isArray(raw.obligations)) throw new GameDomainError(`${path} obligations must be an array`)
  if (!Array.isArray(raw.puzzles)) throw new GameDomainError(`${path} puzzles must be an array`)
  return {
    obligations: raw.obligations.map((entry, index) => {
      const obligation = record(entry, `${path} obligation ${index}`)
      return {
        id: nonempty(obligation.id, `${path} obligation ${index} id`),
        family: nonempty(obligation.family, `${path} obligation ${index} family`),
        distinction: nonempty(obligation.distinction, `${path} obligation ${index} distinction`),
        stoppingRule: nonempty(obligation.stoppingRule, `${path} obligation ${index} stoppingRule`),
      }
    }),
    puzzles: raw.puzzles.map((entry, index) => {
      const row = record(entry, `${path} puzzle ${index}`)
      const immediateComplementPattern = row.immediateComplementPattern === undefined
        ? undefined
        : nonempty(
            row.immediateComplementPattern,
            `${path} puzzle '${String(row.puzzle)}' immediateComplementPattern`,
          )
      return {
        puzzle: puzzleId(nonempty(row.puzzle, `${path} puzzle ${index} id`)),
        obligations: strings(row.obligations, `${path} puzzle '${String(row.puzzle)}' obligations`),
        visibleSituation: nonempty(row.visibleSituation, `${path} puzzle '${String(row.puzzle)}' visibleSituation`),
        defeats: nonempty(row.defeats, `${path} puzzle '${String(row.puzzle)}' defeats`),
        experientialNeighbors: strings(
          row.experientialNeighbors,
          `${path} puzzle '${String(row.puzzle)}' experientialNeighbors`,
        ).map(puzzleId),
        ...(immediateComplementPattern === undefined ? {} : { immediateComplementPattern }),
      }
    }),
  }
}

export function validateGameContent(contentRoot = resolve(process.cwd(), 'content')): ContentValidationReceipt {
  const schemaRoot = resolve(contentRoot, 'schemas')
  const schemas = {
    diagram: parseSchema(resolve(schemaRoot, 'diagram.schema.json')),
    manifest: parseSchema(resolve(schemaRoot, 'manifest.schema.json')),
    puzzle: parseSchema(resolve(schemaRoot, 'puzzle.schema.json')),
    definition: parseSchema(resolve(schemaRoot, 'definition.schema.json')),
    progression: parseSchema(resolve(schemaRoot, 'progression.schema.json')),
    coverage: parseSchema(resolve(schemaRoot, 'coverage.schema.json')),
    catalog: parseSchema(resolve(schemaRoot, 'catalog.schema.json')),
    guidance: parseSchema(resolve(schemaRoot, 'guidance.schema.json')),
    validation: parseSchema(resolve(schemaRoot, 'validation.schema.json')),
  }
  const ajv = new Ajv2020({ allErrors: true, strict: true })
  ajv.addSchema(schemas.diagram)
  const validators = {
    manifest: ajv.compile(schemas.manifest), puzzle: ajv.compile(schemas.puzzle),
    definition: ajv.compile(schemas.definition), progression: ajv.compile(schemas.progression),
    coverage: ajv.compile(schemas.coverage),
    catalog: ajv.compile(schemas.catalog), guidance: ajv.compile(schemas.guidance),
    validation: ajv.compile(schemas.validation),
  }

  const manifest = parseJson(resolve(contentRoot, 'manifest.json'))
  requireSchema(validators.manifest, manifest, 'manifest.json')
  const manifestRecord = record(manifest, 'manifest.json')
  const puzzlePaths = strings(manifestRecord.puzzles, 'manifest puzzles')
  const definitionPaths = strings(manifestRecord.definitions, 'manifest definitions')
  const progressionPath = String(manifestRecord.progression)
  const coverageManifest = record(manifestRecord.coverage, 'manifest coverage')
  const catalogPath = String(manifestRecord.catalog)
  const guidancePath = String(manifestRecord.guidance)
  const runtimeFiles: Record<string, unknown> = { 'manifest.json': manifest }
  for (const path of puzzlePaths) {
    const value = parseJson(resolve(contentRoot, path))
    requireSchema(validators.puzzle, value, path)
    runtimeFiles[path] = value
  }
  for (const path of definitionPaths) {
    const value = parseJson(resolve(contentRoot, path))
    requireSchema(validators.definition, value, path)
    runtimeFiles[path] = value
  }
  for (const [path, validator] of [
    [progressionPath, validators.progression], [catalogPath, validators.catalog], [guidancePath, validators.guidance],
  ] as const) {
    const value = parseJson(resolve(contentRoot, path))
    requireSchema(validator, value, path)
    runtimeFiles[path] = value
  }
  const coverageByCulture = new Map<CultureId, ReturnType<typeof parseCoverage>>()
  for (const [rawCulture, rawPath] of Object.entries(coverageManifest)) {
    const culture = cultureId(rawCulture)
    const path = nonempty(rawPath, `manifest coverage '${rawCulture}'`)
    const value = parseJson(resolve(contentRoot, path))
    requireSchema(validators.coverage, value, path)
    runtimeFiles[path] = value
    coverageByCulture.set(culture, parseCoverage(value, path))
  }
  const catalog = loadGameContent(runtimeFiles as GameContentFiles)

  const puzzleIds = new Set(catalog.puzzleIds)
  const seyricCulture = cultureId('seyric-horizon')
  for (const culture of catalog.cultureIds) {
    const label = catalog.culture(culture).shortName
    const ownedPuzzleIds = catalog.puzzlesInCulture(culture)
    const ownedPuzzleSet = new Set(ownedPuzzleIds)
    const coverage = coverageByCulture.get(culture)
    if (coverage === undefined) throw new GameDomainError(`${label} has no manifest-owned coverage file`)
    const rowsByPuzzle = new Map<PuzzleId, CoverageRow[]>()
    for (const row of coverage.puzzles) {
      rowsByPuzzle.set(row.puzzle, [...(rowsByPuzzle.get(row.puzzle) ?? []), row])
    }
    for (const row of coverage.puzzles) {
      if (!puzzleIds.has(row.puzzle)) {
        throw new GameDomainError(`${label} coverage row names unknown puzzle '${row.puzzle}'`)
      }
      if (!ownedPuzzleSet.has(row.puzzle)) {
        throw new GameDomainError(
          `${label} coverage row names puzzle '${row.puzzle}' owned by '${catalog.placement(row.puzzle).culture}'`,
        )
      }
      if (culture !== seyricCulture && row.immediateComplementPattern !== undefined) {
        throw new GameDomainError(
          `${label} coverage for '${row.puzzle}' uses immediateComplementPattern, which is Seyric-only`,
        )
      }
    }
    for (const id of ownedPuzzleIds) {
      const rows = rowsByPuzzle.get(id) ?? []
      if (rows.length === 0) throw new GameDomainError(`${label} puzzle '${id}' has no coverage row`)
      if (rows.length > 1) throw new GameDomainError(`${label} puzzle '${id}' must have exactly one coverage row`)
    }

    const knownObligations = new Set<string>()
    for (const obligation of coverage.obligations) {
      if (knownObligations.has(obligation.id)) {
        throw new GameDomainError(`duplicate ${label} coverage obligation '${obligation.id}'`)
      }
      knownObligations.add(obligation.id)
    }
    const coveredObligations = new Set<string>()
    for (const row of coverage.puzzles) {
      for (const obligation of row.obligations) {
        if (!knownObligations.has(obligation)) {
          throw new GameDomainError(`${label} coverage for '${row.puzzle}' names unknown obligation '${obligation}'`)
        }
        coveredObligations.add(obligation)
      }
      for (const neighbor of row.experientialNeighbors) {
        if (!puzzleIds.has(neighbor)) {
          throw new GameDomainError(`${label} coverage for '${row.puzzle}' names missing experiential neighbor '${neighbor}'`)
        }
      }
    }
    for (const obligation of knownObligations) {
      if (!coveredObligations.has(obligation)) {
        throw new GameDomainError(`uncovered ${label} obligation '${obligation}'`)
      }
    }
  }

  const seyricIds = catalog.puzzlesInCulture(seyricCulture)

  const seyricByFingerprint = new Map<string, PuzzleId[]>()
  for (const id of seyricIds) {
    const fingerprint = catalog.puzzleFingerprint(id)
    seyricByFingerprint.set(fingerprint, [...(seyricByFingerprint.get(fingerprint) ?? []), id])
  }
  const duplicateSeyricProblems = [...seyricByFingerprint.values()].filter((ids) => ids.length > 1)
  if (duplicateSeyricProblems.length > 0) {
    throw new GameDomainError(`duplicate canonical start among Seyric puzzles: ${duplicateSeyricProblems.map((ids) => ids.join(', ')).join('; ')}`)
  }

  const permittedShortcutPuzzles = new Set<PuzzleId>([
    puzzleId('forked-veil'),
    puzzleId('echoed-veil'),
    puzzleId('atomic-fragment-erasure'),
  ])
  for (const id of seyricIds) {
    const hosts = findEmptyCutShortcutHosts(catalog.puzzle(id).diagram)
    if (hosts.length > 0 && !permittedShortcutPuzzles.has(id)) {
      throw new GameDomainError(
        `empty-cut shortcut in '${id}' at negative host(s): ${hosts.join(', ')}`,
      )
    }
  }

  const seyricLanguageViolations: string[] = []
  for (const id of seyricIds) {
    const analysis = analyzeSeyricStart(catalog.puzzle(id).diagram)
    for (const violation of analysis.violations) {
      seyricLanguageViolations.push(`${id} [${violation.code}]: ${violation.detail}`)
    }
  }
  if (seyricLanguageViolations.length > 0) {
    throw new GameDomainError(`Seyric authored starts violate the global-prefix propositional grammar: ${seyricLanguageViolations.join('; ')}`)
  }

  const seyricCoverage = coverageByCulture.get(seyricCulture)
  if (seyricCoverage === undefined) throw new GameDomainError('Seyric has no manifest-owned coverage file')
  const seyricCoverageByPuzzle = new Map(
    seyricCoverage.puzzles.map((row) => [row.puzzle, row] as const),
  )
  const seyricByMatrixStructure = new Map<string, PuzzleId[]>()
  const immediatePatternOwners = new Map<string, PuzzleId>()
  for (const id of seyricIds) {
    const shape = analyzeSeyricPropositionalShape(catalog.puzzle(id).diagram)
    seyricByMatrixStructure.set(shape.quantifierOrderFingerprint, [
      ...(seyricByMatrixStructure.get(shape.quantifierOrderFingerprint) ?? []),
      id,
    ])

    const pattern = seyricCoverageByPuzzle.get(id)?.immediateComplementPattern
    if (shape.immediateComplement && pattern === undefined) {
      throw new GameDomainError(
        `Seyric puzzle '${id}' exposes an exact graphical sibling occurrence but has no immediateComplementPattern`,
      )
    }
    if (!shape.immediateComplement && pattern !== undefined) {
      throw new GameDomainError(
        `Seyric puzzle '${id}' does not expose an exact graphical sibling occurrence but declares immediateComplementPattern '${pattern}'`,
      )
    }
    if (pattern !== undefined) {
      const prior = immediatePatternOwners.get(pattern)
      if (prior !== undefined) {
        throw new GameDomainError(
          `duplicate exact-sibling-occurrence pattern '${pattern}' for Seyric puzzles '${prior}' and '${id}'`,
        )
      }
      immediatePatternOwners.set(pattern, id)
    }
  }
  const duplicateSeyricMatrices = [...seyricByMatrixStructure.values()]
    .filter((ids) => ids.length > 1)
  if (duplicateSeyricMatrices.length > 0) {
    throw new GameDomainError(
      `duplicate Seyric matrix structure modulo global-prefix order: ${duplicateSeyricMatrices
        .map((ids) => ids.join(', ')).join('; ')}`,
    )
  }

  const evidencePaths = readdirSync(resolve(contentRoot, 'validation'))
    .filter((path) => path.endsWith('.json')).sort()
  const evidence = evidencePaths.map((name) => {
    const path = `validation/${name}`
    const value = parseJson(resolve(contentRoot, path))
    requireSchema(validators.validation, value, path)
    return parseEvidence(value, path)
  })
  if (evidence.length !== catalog.puzzleIds.length) throw new GameDomainError('validation must contain exactly one sidecar per puzzle')
  const byPuzzle = new Map(evidence.map((entry) => [entry.puzzle, entry] as const))
  if (byPuzzle.size !== evidence.length || catalog.puzzleIds.some((id) => !byPuzzle.has(id))) {
    throw new GameDomainError('validation sidecars must name every puzzle exactly once')
  }

  const verified = new Set<PuzzleId>()
  let recognizedCount = 0
  const pending = new Set(catalog.puzzleIds)
  while (pending.size > 0) {
    const next = [...pending].find((id) => catalog.placement(id).prerequisites.every((parent) => verified.has(parent)))
    if (next === undefined) throw new GameDomainError('validation order cannot satisfy puzzle prerequisites')
    const sidecar = byPuzzle.get(next)!
    const closure = new Set<PuzzleId>()
    const add = (id: PuzzleId): void => {
      if (closure.has(id)) return
      closure.add(id)
      for (const parent of catalog.placement(id).prerequisites) add(parent)
    }
    for (const parent of catalog.placement(next).prerequisites) add(parent)
    for (const artifact of sidecar.availableArtifacts) {
      if (!closure.has(artifact) || !verified.has(artifact)) {
        throw new GameDomainError(`validation '${next}' uses artifact '${artifact}' not guaranteed by prerequisite closure`)
      }
    }
    const usedRules = new Set(sidecar.solution.map(({ rule }) => rule))
    const expectedRules = new Set(sidecar.expectedRules)
    if (usedRules.size !== expectedRules.size || [...usedRules].some((rule) => !expectedRules.has(rule))) {
      throw new GameDomainError(`validation '${next}' expectedRules does not equal solution rules`)
    }
    if (catalog.placement(next).culture === seyricCulture) {
      const witnessAudit = auditSeyricWitness(catalog.puzzle(next).diagram, sidecar.solution)
      if (!witnessAudit.ok) {
        throw new GameDomainError(
          `validation '${next}' violates terminal Seyric quantifier cleanup: ${witnessAudit.violations.map(({ detail }) => detail).join('; ')}`,
        )
      }
    }
    const authority = { context: artifactTheoremContext(catalog, new Set(sidecar.availableArtifacts)) }
    let solution = startPuzzle(catalog.puzzle(next))
    for (const step of sidecar.solution) solution = applyGameSteps(solution, [step], authority).session
    if (!isBlank(currentDiagram(solution))) throw new GameDomainError(`validation '${next}' solution does not reach canonical blank`)

    const recognized = catalog.guidance(next).interventions.filter(({ trigger }) => trigger.kind === 'recognizedUnwinnable')
    if (recognized.length !== sidecar.recognizedStates.length) throw new GameDomainError(`validation '${next}' recognized-state demonstrations do not match guidance`)
    for (const demonstration of sidecar.recognizedStates) {
      const intervention = recognized.find(({ id }) => id === demonstration.intervention)
      if (intervention?.trigger.kind !== 'recognizedUnwinnable') throw new GameDomainError(`validation '${next}' names unknown recognized intervention '${demonstration.intervention}'`)
      let reached = startPuzzle(catalog.puzzle(next))
      for (const step of demonstration.demonstration) reached = applyGameSteps(reached, [step], authority).session
      if (exploreForm(currentDiagram(reached)) !== exploreForm(intervention.trigger.state.diagram)) {
        throw new GameDomainError(`validation '${next}' demonstration does not reach '${demonstration.intervention}'`)
      }
      recognizedCount += 1
    }
    verified.add(next)
    pending.delete(next)
  }
  return { puzzles: catalog.puzzleIds.length, solutions: evidence.length, recognizedStates: recognizedCount }
}

const invokedPath = process.argv[1]
if (invokedPath !== undefined && import.meta.url === pathToFileURL(resolve(invokedPath)).href) {
  const receipt = validateGameContent()
  console.log(`Validated ${receipt.puzzles} puzzles, ${receipt.solutions} solutions, and ${receipt.recognizedStates} recognized states.`)
}
