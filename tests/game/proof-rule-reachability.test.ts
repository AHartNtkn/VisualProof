import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { applyAction, type ProofAction } from '../../src/kernel/proof/action'
import { EMPTY_PROOF_CONTEXT } from '../../src/kernel/proof/context'
import type { ProofStep } from '../../src/kernel/proof/step'
import { parseTerm } from '../../src/kernel/term/parse'
import { GameProofMoveController } from '../../src/game/interface/proof-moves'
import { addRelationTerm, currentRelationDraft, insertOptionalPort } from '../../src/interaction/relation-workspace-draft'
import { AbstractTransaction } from '../../src/interaction/relation-transactions'
import { mkEngine } from '../../src/view/engine'
import { DARK } from '../../src/view/paint'
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
  'relUnfold', 'relationSpawn', 'vacuousElim', 'vacuousIntro',
  'wireJoin', 'wireSever',
] as const satisfies readonly Exclude<ProofStep['rule'], 'theorem'>[]

const routeOwners: Record<GameProofInteractionRoute, string> = {
  'empty-space-menu': 'GameProofMoveController.contextMenu',
  'selection-menu': 'GameProofMoveController.contextMenu',
  'selection-key': 'GameProofMoveController.keyDown',
  'wire-key-or-double-click': 'GameProofMoveController.keyDown/doubleClick',
  'selection-drag': 'GameProofMoveController.claim',
  'line-drag': 'ConnectionDragController/FissionDragController',
  'line-menu': 'GameProofMoveController.contextMenu',
  'construction-loupe': 'ConstructionLoupe',
}

describe('game proof-rule reachability contract', () => {
  it('assigns every game-exposed kernel rule to an owned user interaction route', () => {
    const routed = Object.keys(GAME_PROOF_RULE_ROUTES).sort()
    expect(routed).toEqual([...expectedRules].sort())
    expect(routed).toHaveLength(25)
    expect(routed).not.toContain('theorem')
    for (const route of Object.values(GAME_PROOF_RULE_ROUTES)) {
      expect(routeOwners[route]).toBeTruthy()
    }
  })

  it('drives the declared comprehensionAbstract route through a real backward kernel action', () => {
    const builder = new DiagramBuilder()
    const negative = builder.cut(builder.root)
    const node = builder.termNode(negative, parseTerm('\\x. x'))
    builder.wire(negative, [{ node, port: { kind: 'output' } }])
    const diagram = builder.build()
    const actions: ProofAction[] = []
    const controller = new GameProofMoveController({
      host: { ownerDocument: {} } as HTMLElement,
      active: () => true,
      diagram: () => diagram,
      engine: () => mkEngine(diagram, []),
      viewScale: () => 1,
      selection: () => [{ kind: 'node', id: node }],
      setSelection: () => undefined,
      context: () => EMPTY_PROOF_CONTEXT,
      apply: () => { throw new Error('Shift+W must not apply before workspace finalization') },
      refuse: (message) => { throw new Error(message) },
      theme: () => DARK,
      fuel: () => 128,
      openConstruction: () => undefined,
      openAbstraction: (wrap) => {
        const transaction = new AbstractTransaction({
          diagram: () => diagram,
          boundary: () => [],
          wrap,
          context: () => EMPTY_PROOF_CONTEXT,
          orientation: 'backward',
          apply: (action) => { actions.push(action) },
          cancel: () => {},
          engine: () => mkEngine(diagram, []),
          theme: () => DARK,
          matcherFuel: () => 128,
          solverFuel: () => 1024,
        })
        let draft = addRelationTerm(transaction.initialDraft(), parseTerm('\\x. x'))
        const wire = Object.keys(currentRelationDraft(draft).diagram.wires)[0]!
        draft = insertOptionalPort(draft, wire, 0)
        transaction.finalize(currentRelationDraft(draft), [])
      },
    })

    expect(controller.keyDown({
      key: 'W', shiftKey: true, ctrlKey: false, altKey: false, metaKey: false, repeat: false,
    })).toBe(true)
    expect(actions).toHaveLength(1)
    expect(actions[0]!.steps).toEqual([expect.objectContaining({ rule: 'comprehensionAbstract' })])
    expect(() => applyAction(diagram, actions[0]!, EMPTY_PROOF_CONTEXT, 'backward')).not.toThrow()
  })
})
