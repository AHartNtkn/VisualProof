import type { DiagramWithBoundary } from '../kernel/diagram/boundary'
import type { RegionId } from '../kernel/diagram/diagram'
import type { SubgraphSelection } from '../kernel/diagram/subgraph/selection'
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

export type GameKernelStep = ProofStep

export type VellumStep =
  | { readonly rule: 'vellumManifest'; readonly puzzle: PuzzleId; readonly region: RegionId }
  | { readonly rule: 'vellumDissolve'; readonly puzzle: PuzzleId; readonly selection: SubgraphSelection }

export type GameStep = GameKernelStep | VellumStep

export type GameRuleContext = Pick<ProofContext, 'relations'>

export type PuzzleDefinition = {
  readonly id: PuzzleId
  readonly culture: CultureId
  readonly title: string
  readonly goal: DiagramWithBoundary
  readonly prerequisites: readonly PuzzleId[]
  readonly grantsVellum: boolean
  readonly witness: readonly GameStep[]
}

export type CultureDefinition = { readonly id: CultureId; readonly name: string }

export type GameCatalogSource = {
  readonly cultures: readonly CultureDefinition[]
  readonly puzzles: readonly PuzzleDefinition[]
  readonly context: GameRuleContext
}
