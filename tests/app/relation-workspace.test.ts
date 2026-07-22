import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { parseTerm } from '../../src/kernel/term/parse'
import { mkDiagram, type Diagram } from '../../src/kernel/diagram/diagram'
import { applyAction, type ProofAction } from '../../src/kernel/proof/action'
import { EMPTY_PROOF_CONTEXT, type ProofContext } from '../../src/kernel/proof/context'
import {
  applyCapturedRelationConnection,
  applyRelationWorkspaceCopy,
  arbitrateRelationHostCopy,
  applyPortStripDelete,
  applyPortStripDrop,
  applyPortStripMove,
  moveRelationWorkspace,
  placeRelationWorkspace,
  previewRelationWorkspaceSnapshot,
  relationConnectionTargets,
  relationWorkspaceWorldPoint,
  relationWorkspaceCanFinalize,
  resizeRelationWorkspace,
  SubstituteTransaction,
} from '../../src/interaction/relation-workspace'
import {
  beginAbstractionDraft,
  beginSubstitutionDraft,
  currentRelationDraft,
  importRelationHostBinderOccurrence,
  replaceRelationDiagram,
} from '../../src/interaction/relation-workspace-draft'
import { planCopy } from '../../src/interaction/copy-planner'

const context = (): ProofContext => (EMPTY_PROOF_CONTEXT)

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
  it('uses a transaction still click but yields a moved occurrence gesture to copy', () => {
    const events: string[] = []
    const claim = (name: string): import('../../src/interaction/controllers/viewport').PointerClaim => ({
      still: 'claim', blocksPassiveRelaxation: false,
      move: () => { events.push(`${name}:move`) },
      release: (_sample, moved) => { events.push(`${name}:release:${moved}`) },
      cancel: () => { events.push(`${name}:cancel`) },
    })
    const pointer = {
      pointerId: 1, button: 0, client: { x: 0, y: 0 }, screen: { x: 0, y: 0 }, world: { x: 0, y: 0 },
      hit: null, shiftKey: false, ctrlKey: false, altKey: false, metaKey: false,
    }

    const still = arbitrateRelationHostCopy(claim('transaction'), claim('copy'))
    still.release(pointer, false)
    expect(events).toEqual(['copy:cancel', 'transaction:release:false'])

    events.length = 0
    const moved = arbitrateRelationHostCopy(claim('transaction'), claim('copy'))
    moved.move(pointer)
    moved.release(pointer, true)
    expect(events).toEqual(['copy:move', 'transaction:cancel', 'copy:release:true'])
  })

  it('converts host-drop client coordinates into workspace world coordinates', () => {
    expect(relationWorkspaceWorldPoint(
      { x: 250, y: 180 },
      { left: 100, top: 80, width: 300, height: 200 },
      { width: 600, height: 400 },
      { scale: 2, offsetX: 100, offsetY: 60 },
    )).toEqual({ x: 100, y: 70 })
  })

  it('records a workspace copy as exactly one draft snapshot', () => {
    const sourceBuilder = new DiagramBuilder()
    const node = sourceBuilder.termNode(sourceBuilder.root, parseTerm('x'))
    const source = sourceBuilder.build()
    const selection = mkSelection(source, { region: source.root, regions: [], nodes: [node], wires: [] })
    const draft = beginAbstractionDraft(source)
    const before = currentRelationDraft(draft)
    const planned = planCopy(source, selection, {
      kind: 'workspace', draft: before.diagram, region: before.diagram.root, at: { x: 3, y: 4 },
    })
    if (planned.kind === 'refusal') throw new Error(planned.message)

    const copied = applyRelationWorkspaceCopy(draft, planned)
    expect(copied.cursor).toBe(draft.cursor + 1)
    expect(copied.history).toHaveLength(draft.history.length + 1)
    expect(currentRelationDraft(copied).diagram).toBe(planned.kind === 'workspace' ? planned.result : null)
    expect(currentRelationDraft(copied).ports).toEqual([])
    const copiedWires = Object.values(currentRelationDraft(copied).diagram.wires)
    expect(copiedWires).toHaveLength(2)
    expect(copiedWires.every((wire) => wire.scope === currentRelationDraft(copied).diagram.root)).toBe(true)
    expect(copiedWires.every((wire) => wire.endpoints.length === 1)).toBe(true)
  })

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
    const host = hostWithBubble(0)
    let draft = beginSubstitutionDraft(host, 'bubble')
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

    expect(ready).toEqual({ kind: 'ready', code: 'ready', message: 'ready to instantiate' })
    transaction.finalize(currentRelationDraft(draft), [])
    expect(actions).toEqual([{
      label: 'substitute relation',
      steps: [expect.objectContaining({
        rule: 'comprehensionInstantiate', bubble: 'bubble', attachments: ['h1'], binders: [],
      })],
      placements: [],
    }])
    expect(cancelled).toEqual([])

  })

  it('dry-runs and applies the exact nonempty materialized binder array', () => {
    const builder = new DiagramBuilder()
    const hostBinder = builder.bubble(builder.root, 0)
    const guard = builder.cut(hostBinder)
    const target = builder.bubble(guard, 0)
    builder.atom(target, target)
    const current = builder.build()
    const actions: ProofAction[] = []
    const transaction = new SubstituteTransaction({
      diagram: () => current,
      boundary: () => [],
      bubble: target,
      context,
      apply: (action) => { actions.push(action) },
      cancel: () => {},
    })
    const draft = importRelationHostBinderOccurrence(transaction.initialDraft(), hostBinder)
    const pair = currentRelationDraft(draft).comprehension?.dependencies[0]
    if (pair === undefined) throw new Error('expected imported binder pair')

    expect(transaction.status(currentRelationDraft(draft))).toEqual({
      kind: 'ready', code: 'ready', message: 'ready to instantiate',
    })
    expect(() => transaction.finalize(currentRelationDraft(draft), [])).not.toThrow()
    expect(actions).toEqual([{
      label: 'substitute relation',
      steps: [{
        rule: 'comprehensionInstantiate',
        bubble: target,
        comp: currentRelationDraft(draft).comprehension?.pattern,
        attachments: [],
        binders: [pair],
      }],
      placements: [],
    }])
    const result = applyAction(current, actions[0]!, context())
    expect(result.regions[target]).toBeUndefined()
    expect(Object.values(result.nodes).some((node) =>
      node.kind === 'atom' && node.binder === hostBinder)).toBe(true)
    expect(Object.values(result.nodes).some((node) =>
      node.kind === 'atom' && node.binder === target)).toBe(false)
  })
})
