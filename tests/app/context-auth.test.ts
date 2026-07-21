import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import type { ProofContext } from '../../src/kernel/proof/context'
import { applicableActions } from '../../src/interaction/actions'
import { defineRelation } from '../../src/interaction/define'
import { instantiationChoices } from '../../src/app/interact/moves'
import { sessionTheory } from '../../src/app/persist'
import { mkReplay } from '../../src/app/replay'
import { startSession, startTrack } from '../../src/app/session'
import { revalidateCopy, type CopyPlan } from '../../src/interaction/copy-planner'

describe('application ProofContext boundaries', () => {
  it('rejects a structural forgery before zero-work or unrelated validation', () => {
    const forged = { theorems: new Map(), relations: new Map() } as unknown as ProofContext
    const diagram = new DiagramBuilder().build()
    const side = mkDiagramWithBoundary(diagram, [])
    const theorem = { name: 'identity', lhs: side, rhs: side, actions: [] }
    const selection = { region: diagram.root, regions: [], nodes: [], wires: [] }
    const calls = [
      () => mkReplay(theorem.name, forged),
      () => startTrack(side, 'forward', forged),
      () => startSession(side, side, forged),
      () => applicableActions(diagram, selection, forged),
      () => instantiationChoices(forged, 0),
      () => sessionTheory(forged, { relations: [] }),
      () => defineRelation(diagram, selection, [], '', forged),
      () => revalidateCopy({} as CopyPlan, diagram, {
        kind: 'proof', diagram, region: 'missing', orientation: 'forward', ctx: forged,
      }),
    ]
    for (const call of calls) expect(call).toThrowError('invalid proof context')
  })
})
