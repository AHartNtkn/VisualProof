import type { DiagramWithBoundary } from '../kernel/diagram/boundary'
import type { RegionId } from '../kernel/diagram/diagram'
import type { SubgraphSelection } from '../kernel/diagram/subgraph/selection'
import type { ProofStep, ProofContext } from '../kernel/proof/step'

export type PuzzleId = string & { readonly __puzzleId: unique symbol }
export type CultureId = string & { readonly __cultureId: unique symbol }
export type PerformanceId = string & { readonly __performanceId: unique symbol }

export const puzzleId = (value: string): PuzzleId => {
  if (!/^[a-z0-9]+(?:-[a-z0-9]+)*$/.test(value)) {
    throw new GameDomainError(`invalid puzzle id '${value}'`)
  }
  return value as PuzzleId
}

export const cultureId = (value: string): CultureId => {
  if (!/^[a-z0-9]+(?:-[a-z0-9]+)*$/.test(value)) {
    throw new GameDomainError(`invalid culture id '${value}'`)
  }
  return value as CultureId
}

export const performanceId = (value: string): PerformanceId => {
  if (!/^[a-z0-9]+(?:-[a-z0-9]+)*$/.test(value)) {
    throw new GameDomainError(`invalid performance id '${value}'`)
  }
  return value as PerformanceId
}

export class GameDomainError extends Error {}

export type GameKernelStep = ProofStep

export type VellumStep =
  | { readonly rule: 'vellumManifest'; readonly puzzle: PuzzleId; readonly region: RegionId }
  | { readonly rule: 'vellumDissolve'; readonly puzzle: PuzzleId; readonly selection: SubgraphSelection }

export type GameStep = GameKernelStep | VellumStep

export type GameRuleContext = Pick<ProofContext, 'relations'>

export type KnowledgePoint = {
  readonly id: string
  readonly instruction: string
  readonly commonError: string
  readonly correction: string
}

export type PerformanceDefinition = {
  readonly id: PerformanceId
  readonly description: string
  readonly prerequisites: readonly PerformanceId[]
  readonly knowledgePoints: readonly KnowledgePoint[]
  readonly masteryEvidence: string
  readonly remediation: readonly PerformanceId[]
}

export type ArtifactName = {
  readonly professional: string
  readonly curatorShorthand?: string
  readonly accession?: string
}

export type ArtifactProvenance = {
  readonly summary: string
  readonly function: string
  readonly findspot?: string
  readonly attributedTo?: string
}

export type TeacherBeat = {
  readonly trigger: 'opening' | 'completion' | 'stuck'
  readonly text: string
}

export type MisconceptionCue = {
  readonly id: string
  readonly performance: PerformanceId
  readonly thought: string
}

export type PuzzleLearning = {
  readonly introduces: readonly PerformanceId[]
  readonly practices: readonly PerformanceId[]
  readonly retrieves: readonly PerformanceId[]
  readonly assesses: readonly PerformanceId[]
  readonly rulesUsed: readonly GameStep['rule'][]
}

export type PuzzleDefinition = {
  readonly id: PuzzleId
  readonly culture: CultureId
  readonly name: ArtifactName
  readonly provenance: ArtifactProvenance
  readonly goal: DiagramWithBoundary
  readonly prerequisites: readonly PuzzleId[]
  readonly grantsVellum: boolean
  readonly witness: readonly GameStep[]
  readonly learning: PuzzleLearning
  readonly teacher: readonly TeacherBeat[]
  readonly misconceptions: readonly MisconceptionCue[]
}

export type CultureDefinition = {
  readonly id: CultureId
  readonly name: string
  readonly relativeAge: number
  readonly historicalSummary: string
  readonly lineage: readonly CultureId[]
  readonly isolation: 'connected' | 'isolated' | 'uncertain'
  readonly sealingVocabulary: readonly string[]
  readonly unlocksAfter: readonly PuzzleId[]
  readonly gateway: PuzzleId
}

export type GameCatalogSource = {
  readonly cultures: readonly CultureDefinition[]
  readonly performances: readonly PerformanceDefinition[]
  readonly puzzles: readonly PuzzleDefinition[]
  readonly context: GameRuleContext
}
