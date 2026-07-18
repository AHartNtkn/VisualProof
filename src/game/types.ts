import type { DiagramWithBoundary } from '../kernel/diagram/boundary'
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

export type GameStep = ProofStep

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

export type TeacherTrigger =
  | { readonly kind: 'opening' }
  | { readonly kind: 'completion' }
  | {
      readonly kind: 'recognizedUnwinnable'
      readonly state: DiagramWithBoundary
      readonly demonstration: readonly GameStep[]
    }

type TeacherInterventionBase = {
  readonly id: string
  readonly performance?: PerformanceId
  readonly text: string
  readonly repeat: 'once' | 'repeatable'
}

export type TeacherIntervention =
  | TeacherInterventionBase & {
      readonly trigger: Extract<TeacherTrigger, { readonly kind: 'opening' | 'completion' }>
      readonly recovery?: never
    }
  | TeacherInterventionBase & {
      readonly trigger: Extract<TeacherTrigger, { readonly kind: 'recognizedUnwinnable' }>
      readonly recovery: 'timeline'
    }

export type TeacherAcknowledgementIdentity = {
  readonly puzzle: PuzzleId
  readonly intervention: string
}

export const teacherAcknowledgementIdentity = (
  puzzle: PuzzleId,
  intervention: string,
): TeacherAcknowledgementIdentity => ({ puzzle, intervention })

export const isTeacherAcknowledged = (
  acknowledged: readonly TeacherAcknowledgementIdentity[],
  identity: TeacherAcknowledgementIdentity,
): boolean => acknowledged.some((candidate) =>
  candidate.puzzle === identity.puzzle
  && candidate.intervention === identity.intervention)

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
  readonly witness: readonly GameStep[]
  readonly learning: PuzzleLearning
  readonly teacher: readonly TeacherIntervention[]
}

export type CultureDefinition = {
  readonly id: CultureId
  readonly name: string
  readonly shortName?: string
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
