import { describe, expect, it } from 'vitest'
import type { ProofStep } from '../../src/kernel/proof/step'
import {
  GAME_PROOF_RULE_ROUTES,
  type GameProofInteractionRoute,
} from '../../src/game/interface/proof-rule-routes'

const expectedRules = [
  'anchoredWireContract', 'anchoredWireSplit', 'boundRelationSpawn',
  'closedTermIntro', 'comprehensionAbstract', 'comprehensionInstantiate',
  'congruenceJoin', 'conversion', 'deiteration', 'doubleCutElim',
  'doubleCutIntro', 'erasure', 'fission', 'fusion', 'headStrip',
  'inconsistentCutElim', 'iteration', 'openTermSpawn', 'relFold',
  'relUnfold', 'relationSpawn', 'theorem', 'vacuousElim', 'vacuousIntro',
  'wireJoin', 'wireSever',
] as const satisfies readonly ProofStep['rule'][]

const routeOwners: Record<GameProofInteractionRoute, string> = {
  'empty-space-menu': 'GameProofMoveController.contextMenu',
  'selection-menu': 'GameProofMoveController.contextMenu',
  'selection-key': 'GameProofMoveController.keyDown',
  'wire-key-or-double-click': 'GameProofMoveController.keyDown/doubleClick',
  'selection-drag': 'GameProofMoveController.claim',
  'line-drag': 'ConnectionDragController/FissionDragController',
  'line-menu': 'GameProofMoveController.contextMenu',
  'construction-loupe': 'ConstructionLoupe',
  'artifact-drop': 'GameProofViewport.dropArtifact',
}

describe('game proof-rule reachability contract', () => {
  it('assigns all 26 kernel rules to an owned user interaction route', () => {
    const routed = Object.keys(GAME_PROOF_RULE_ROUTES).sort()
    expect(routed).toEqual([...expectedRules].sort())
    expect(routed).toHaveLength(26)
    for (const route of Object.values(GAME_PROOF_RULE_ROUTES)) {
      expect(routeOwners[route]).toBeTruthy()
    }
  })
})
