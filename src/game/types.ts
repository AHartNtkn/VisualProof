import type { DiagramWithBoundary } from '../kernel/diagram/boundary'
import type { Diagram } from '../kernel/diagram/diagram'
import type { ProofStep, ProofContext } from '../kernel/proof/step'

export type PuzzleId = string & { readonly __puzzleId: unique symbol }
export type CultureId = string & { readonly __cultureId: unique symbol }

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

export class GameDomainError extends Error {}

export type GameStep = ProofStep
export type GameSteps = readonly [GameStep, ...GameStep[]]

export type GameRuleContext = Pick<ProofContext, 'relations'>

export type PuzzleDefinition = {
  readonly id: PuzzleId
  readonly diagram: Diagram
}

export type PuzzlePlacement = {
  readonly puzzle: PuzzleId
  readonly culture: CultureId
  readonly prerequisites: readonly PuzzleId[]
}

export type ProgressionCultureDefinition = {
  readonly id: CultureId
  readonly order: number
  readonly unlocksAfter: readonly PuzzleId[]
  readonly gateway: PuzzleId
  readonly puzzles: readonly PuzzleId[]
}

export type ArtifactDefinition = {
  readonly puzzle: PuzzleId
  readonly name: ArtifactName
  readonly provenance: ArtifactProvenance
}

export type CatalogCultureDefinition = {
  readonly id: CultureId
  readonly name: string
  readonly shortName: string
  readonly relativeAge: number
  readonly historicalSummary: string
  readonly lineage: readonly CultureId[]
  readonly isolation: 'connected' | 'isolated' | 'uncertain'
  readonly sealingVocabulary: readonly string[]
}

export type GuidanceTrigger =
  | { readonly kind: 'opening' }
  | { readonly kind: 'completion' }
  | { readonly kind: 'recognizedUnwinnable'; readonly state: DiagramWithBoundary }

type GuidanceInterventionBase = {
  readonly id: string
  readonly pages: readonly string[]
  readonly repeat: 'once' | 'repeatable'
}

export type GuidanceIntervention =
  | GuidanceInterventionBase & {
      readonly trigger: Extract<GuidanceTrigger, { readonly kind: 'opening' | 'completion' }>
      readonly recovery?: never
    }
  | GuidanceInterventionBase & {
      readonly trigger: Extract<GuidanceTrigger, { readonly kind: 'recognizedUnwinnable' }>
      readonly recovery: 'timeline'
    }

export type GuidanceDefinition = {
  readonly puzzle: PuzzleId
  readonly interventions: readonly GuidanceIntervention[]
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

export type GuidanceDeliveryIdentity = {
  readonly puzzle: PuzzleId
  readonly intervention: string
}

export const guidanceDeliveryIdentity = (
  puzzle: PuzzleId,
  intervention: string,
): GuidanceDeliveryIdentity => ({ puzzle, intervention })

export const isGuidanceDelivered = (
  delivered: readonly GuidanceDeliveryIdentity[],
  identity: GuidanceDeliveryIdentity,
): boolean => delivered.some((candidate) =>
  candidate.puzzle === identity.puzzle
  && candidate.intervention === identity.intervention)
