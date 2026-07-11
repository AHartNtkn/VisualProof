import type { DiagramWithBoundary } from '../kernel/diagram/boundary'
import type { RegionId } from '../kernel/diagram/diagram'
import type { SubgraphSelection } from '../kernel/diagram/subgraph/selection'
import type { ProofStep, ProofContext } from '../kernel/proof/step'

export type PuzzleId = string & { readonly __puzzleId: unique symbol }
export type CampaignId = string & { readonly __campaignId: unique symbol }

export const puzzleId = (value: string): PuzzleId => {
  if (!/^[a-z0-9]+(?:-[a-z0-9]+)*$/.test(value)) {
    throw new GameDomainError(`invalid puzzle id '${value}'`)
  }
  return value as PuzzleId
}

export const campaignId = (value: string): CampaignId => {
  if (!/^[a-z0-9]+(?:-[a-z0-9]+)*$/.test(value)) {
    throw new GameDomainError(`invalid campaign id '${value}'`)
  }
  return value as CampaignId
}

export class GameDomainError extends Error {}

export type GameKernelStep = ProofStep

export type VellumStep =
  | { readonly rule: 'vellumManifest'; readonly puzzle: PuzzleId; readonly region: RegionId }
  | { readonly rule: 'vellumDissolve'; readonly puzzle: PuzzleId; readonly selection: SubgraphSelection }

export type GameStep = GameKernelStep | VellumStep

export type GameRuleContext = Pick<ProofContext, 'relations'>

export type PuzzleDefinition = {
  readonly id: PuzzleId
  readonly campaign: CampaignId
  readonly title: string
  readonly goal: DiagramWithBoundary
  readonly prerequisites: readonly PuzzleId[]
  readonly grantsVellum: boolean
  readonly witness: readonly GameStep[]
}

export type CampaignDefinition = {
  readonly id: CampaignId
  readonly title: string
}

export type GameCatalogSource = {
  readonly campaigns: readonly CampaignDefinition[]
  readonly puzzles: readonly PuzzleDefinition[]
  readonly context: GameRuleContext
}
