import { describe, expect, it } from 'vitest'
import { mkDiagram, type Diagram } from '../../src/kernel/diagram/diagram'
import type { ProofAction } from '../../src/kernel/proof/action'
import type { ProofContext } from '../../src/kernel/proof/step'
import {
  applyCapturedRelationConnection,
  applyPortStripDelete,
  applyPortStripDrop,
  applyPortStripMove,
  moveRelationWorkspace,
  placeRelationWorkspace,
  previewRelationWorkspaceSnapshot,
  relationConnectionTargets,
  relationWorkspaceCanFinalize,
  resizeRelationWorkspace,
  SubstituteTransaction,
} from '../../src/app/relation-workspace'
import {
  beginAbstractionDraft,
  beginSubstitutionDraft,
  currentRelationDraft,
  replaceRelationDiagram,
} from '../../src/app/relation-workspace-draft'

const context = (): ProofContext => ({ theorems: new Map(), relations: new Map() })

function hostWithBubble(arity = 2): Diagram {
  return mkDiagram({
    root: 'r0',
    regions: {
      r0: { kind: 'sheet' },
      bubble: { kind: 'bubble', parent: 'r0', arity },
    },
    wires: {
      h1: { scope: 'r0', endpoints: [] },
      h2: { scope: 'r0', endpoints: [] },
    },
  })
}

describe('shared relation workspace mechanics', () => {
  it('retains one geometry implementation for every transaction configuration', () => {
    expect(placeRelationWorkspace({ x: 300, y: 300 }, { width: 1400, height: 900 })).toEqual({
      left: 316, top: 282, width: 660, height: 560,
    })
    expect(placeRelationWorkspace({ x: 1200, y: 300 }, { width: 1400, height: 900 })).toEqual({
      left: 524, top: 282, width: 660, height: 560,
    })
    expect(placeRelationWorkspace({ x: 640, y: 360 }, { width: 1280, height: 720 })).toEqual({
      left: 656, top: 126, width: 612, height: 560,
    })
    expect(placeRelationWorkspace({ x: 10, y: 10 }, { width: 400, height: 360 })).toEqual({
      left: 12, top: 44, width: 376, height: 282,
    })
    const base = { left: 200, top: 100, width: 500, height: 400 }
    expect(moveRelationWorkspace(base, { x: 999, y: -999 }, { width: 900, height: 700 })).toEqual({
      left: 400, top: 0, width: 500, height: 400,
    })
    expect(resizeRelationWorkspace(base, { x: -999, y: 999 }, { width: 900, height: 700 })).toEqual({
      left: 200, top: 100, width: 420, height: 600,
    })
  })

  it('inserts on wire-to-strip drop, reorders by port drag, and deletes only optional ports', () => {
    let draft = beginSubstitutionDraft(hostWithBubble(1), 'bubble')
    const initial = currentRelationDraft(draft)
    draft = replaceRelationDiagram(draft, mkDiagram({
      root: initial.diagram.root,
      regions: { ...initial.diagram.regions },
      wires: { ...initial.diagram.wires, w1: { scope: 'r0', endpoints: [] }, w2: { scope: 'r0', endpoints: [] } },
    }))
    draft = applyPortStripDrop(draft, 'w1', 0)
    expect(previewRelationWorkspaceSnapshot(currentRelationDraft(draft)).boundary).toEqual(['arg1', 'w1'])
    draft = applyPortStripDrop(draft, 'w2', 1)
    const [forced, first, second] = currentRelationDraft(draft).ports

    draft = applyPortStripMove(draft, second!.id, 0)
    expect(currentRelationDraft(draft).ports.map((port) => port.wire)).toEqual(['arg1', 'w2', 'w1'])
    expect(() => applyPortStripDelete(draft, forced!.id)).toThrow(/forced port.*cannot be deleted/i)
    draft = applyPortStripDelete(draft, first!.id)
    expect(currentRelationDraft(draft).ports.map((port) => port.wire)).toEqual(['arg1', 'w2'])
  })

  it('shares checked connection targets and rejects a gesture captured from a stale snapshot', () => {
    const host = hostWithBubble()
    let draft = beginAbstractionDraft(host)
    const initial = currentRelationDraft(draft)
    draft = replaceRelationDiagram(draft, mkDiagram({
      root: initial.diagram.root,
      regions: { ...initial.diagram.regions },
      wires: { w1: { scope: 'r0', endpoints: [] }, w2: { scope: 'r0', endpoints: [] } },
    }))
    const captured = currentRelationDraft(draft)
    expect([...relationConnectionTargets(draft, { kind: 'host', wire: 'h1' }).draft]).toEqual(['w1', 'w2'])

    draft = applyPortStripDrop(draft, 'w1', 0)
    expect(() => applyCapturedRelationConnection(
      draft,
      captured,
      { kind: 'host', wire: 'h1' },
      { kind: 'draft', wire: 'w2' },
    )).toThrow(/draft changed/i)
  })

})

describe('substitution transaction', () => {
  it('scratch-checks status and finalizes one labeled proof action with materialized attachments', () => {
    const current = hostWithBubble(1)
    const actions: ProofAction[] = []
    const cancelled: boolean[] = []
    const transaction = new SubstituteTransaction({
      diagram: () => current,
      boundary: () => [],
      bubble: 'bubble',
      context,
      orientation: 'backward',
      apply: (action) => { actions.push(action) },
      cancel: () => { cancelled.push(true) },
    })
    let draft = transaction.initialDraft()
    expect(currentRelationDraft(draft).ports).toEqual([
      { id: 'forced1', wire: 'arg1', kind: 'forced' },
    ])
    const snapshot = currentRelationDraft(draft)
    draft = replaceRelationDiagram(draft, mkDiagram({
      root: snapshot.diagram.root,
      regions: { ...snapshot.diagram.regions },
      wires: { ...snapshot.diagram.wires, extra: { scope: 'r0', endpoints: [] } },
    }))
    const unbound = applyPortStripDrop(draft, 'extra', 0)
    expect(relationWorkspaceCanFinalize(transaction, currentRelationDraft(unbound))).toBe(false)
    draft = applyPortStripDrop(draft, 'extra', 0, 'h1')
    expect(relationWorkspaceCanFinalize(transaction, currentRelationDraft(draft))).toBe(true)
    const ready = transaction.status(currentRelationDraft(draft))

    expect(ready).toEqual({ kind: 'ready', message: 'ready to instantiate' })
    transaction.finalize(currentRelationDraft(draft), [])
    expect(actions).toEqual([{
      label: 'substitute relation',
      steps: [expect.objectContaining({
        rule: 'comprehensionInstantiate', bubble: 'bubble', attachments: ['h1'], binders: {},
      })],
      placements: [],
    }])
    expect(cancelled).toEqual([])

  })
})
