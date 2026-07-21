import type { ProofStep } from '../../kernel/proof/step'

export type GameProofInteractionRoute =
  | 'empty-space-menu'
  | 'selection-menu'
  | 'selection-key'
  | 'wire-key-or-double-click'
  | 'selection-drag'
  | 'line-drag'
  | 'line-menu'
  | 'construction-loupe'

type GameKernelRule = Exclude<ProofStep['rule'], 'theorem'>

/** Exhaustive interaction ownership for every kernel rule exposed by the game.
    General theorem citation is intentionally not a game mechanic; completed
    artifacts use their own exact manifest/dissolve interaction. */
export const GAME_PROOF_RULE_ROUTES = {
  closedTermIntro: 'empty-space-menu',
  openTermSpawn: 'empty-space-menu',
  relationSpawn: 'empty-space-menu',
  boundRelationSpawn: 'empty-space-menu',
  erasure: 'selection-menu',
  doubleCutIntro: 'selection-key',
  doubleCutElim: 'selection-menu',
  vacuousIntro: 'selection-key',
  vacuousElim: 'selection-menu',
  iteration: 'selection-drag',
  deiteration: 'selection-menu',
  inconsistentCutElim: 'selection-menu',
  conversion: 'selection-menu',
  fusion: 'wire-key-or-double-click',
  fission: 'line-drag',
  wireJoin: 'line-drag',
  congruenceJoin: 'line-drag',
  anchoredWireContract: 'line-drag',
  headStrip: 'line-drag',
  wireSever: 'line-menu',
  anchoredWireSplit: 'line-menu',
  comprehensionInstantiate: 'construction-loupe',
  comprehensionAbstract: 'selection-menu',
  relFold: 'selection-menu',
  relUnfold: 'selection-menu',
} as const satisfies Record<GameKernelRule, GameProofInteractionRoute>
