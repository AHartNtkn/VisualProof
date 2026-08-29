import { DiagramBuilder } from '../../kernel/diagram/builder'
import { applyDoubleCutIntro } from '../../kernel/rules/doublecut'
import { snapshotFromDiagram, type DiagramSnapshot } from '../diagram-snapshot'

export type PotPlacement = {
  readonly x: number
  readonly z: number
  readonly yaw: number
}

export type OrderState =
  | { readonly kind: 'pending' }
  | { readonly kind: 'accepted'; readonly pot: PotPlacement }
  | { readonly kind: 'completed' }

export type OrderProgress = {
  readonly reputation: number
  readonly orders: ReadonlyMap<string, OrderState>
}

export type OrderDefinition = {
  readonly id: string
  readonly title: string
  readonly description: string
  readonly reward: number
  readonly goal: DiagramSnapshot
}

const blank = new DiagramBuilder().build()
const starterGoal = snapshotFromDiagram(applyDoubleCutIntro(blank, {
  region: blank.root,
  regions: [],
  nodes: [],
  wires: [],
}))

export const STARTER_ORDER_ID = 'starter-double-cut'

export const ORDER_CATALOG: readonly OrderDefinition[] = Object.freeze([Object.freeze({
  id: STARTER_ORDER_ID,
  title: 'Double Cut',
  description: 'Present a proposition with one empty double cut.',
  reward: 1,
  goal: starterGoal,
})])
