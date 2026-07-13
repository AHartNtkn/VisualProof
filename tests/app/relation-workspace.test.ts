import { describe, expect, it } from 'vitest'
import { mkDiagram, type Diagram } from '../../src/kernel/diagram/diagram'
import { mkDiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import type { ProofAction } from '../../src/kernel/proof/action'
import type { ProofContext } from '../../src/kernel/proof/step'
import {
  applyCapturedRelationConnection,
  applyPortStripDelete,
  applyPortStripDrop,
  applyPortStripMove,
  attemptRelationWorkspaceFinalize,
  clearRelationWorkspaceTransientState,
  editRelationWorkspaceDraft,
  moveRelationWorkspace,
  placeRelationWorkspace,
  portStripInsertionIndex,
  previewRelationWorkspaceSnapshot,
  relationConnectionTargets,
  relationWorkspaceCanFinalize,
  relationBoundaryMarks,
  renderRelationPortStrip,
  resizeRelationWorkspace,
  runRelationWorkspaceCancellation,
  SubstituteTransaction,
  transactionCopy,
  type RelationWorkspaceTransaction,
  type WorkspaceTransientState,
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

function transaction(mode: 'substitute' | 'abstract'): RelationWorkspaceTransaction {
  const diagram = hostWithBubble()
  return {
    mode,
    title: mode === 'substitute' ? 'SUBSTITUTE · NEW RELATION /2' : 'ABSTRACT · SELECT RELATION',
    finalizeLabel: mode === 'substitute' ? 'Instantiate' : 'Abstract',
    sourceDiagram: () => diagram,
    sourceBoundary: () => [],
    previewShapes: () => [],
    status: () => ({ kind: 'ready', message: 'ready' }),
    finalize: () => {},
    cancel: () => {},
  }
}

class ElementStub {
  className = ''
  textContent = ''
  readonly dataset: Record<string, string> = {}
  readonly children: ElementStub[] = []
  readonly attributes = new Map<string, string>()
  readonly classList = { add: (...names: string[]) => {
    this.className = [...new Set(`${this.className} ${names.join(' ')}`.trim().split(/\s+/))].join(' ')
  } }
  append(...children: ElementStub[]): void { this.children.push(...children) }
  setAttribute(name: string, value: string): void { this.attributes.set(name, value) }
}

const stubDocument = {
  createElement: () => new ElementStub(),
} as unknown as Document

describe('shared relation workspace mechanics', () => {
  it('uses transaction configuration for mode copy while retaining one geometry implementation', () => {
    expect(transactionCopy(transaction('substitute'))).toEqual({
      title: 'SUBSTITUTE · NEW RELATION /2',
      finalizeLabel: 'Instantiate',
    })
    expect(transactionCopy(transaction('abstract'))).toEqual({
      title: 'ABSTRACT · SELECT RELATION',
      finalizeLabel: 'Abstract',
    })

    expect(placeRelationWorkspace({ x: 300, y: 300 }, { width: 1400, height: 900 })).toEqual({
      left: 316, top: 282, width: 660, height: 560,
    })
    expect(placeRelationWorkspace({ x: 1200, y: 300 }, { width: 1400, height: 900 })).toEqual({
      left: 524, top: 282, width: 660, height: 560,
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

  it('marks only forced position zero as the orientation reference', () => {
    expect(relationBoundaryMarks(['w2', 'w1', 'w2'])).toEqual([
      { wire: 'w2', position: 0, orientation: true },
      { wire: 'w1', position: 1, orientation: false },
      { wire: 'w2', position: 2, orientation: false },
    ])
  })

  it('renders one real spatial strip with distinct forced and optional port targets', () => {
    const ports = [
      { id: 'forced1', wire: 'arg1', kind: 'forced' },
      { id: 'port1', wire: 'w1', kind: 'optional', hostWire: 'h1' },
    ] as const
    const strip = renderRelationPortStrip(stubDocument, ports) as unknown as ElementStub

    expect(strip.className).toBe('vpa-relation-port-strip')
    expect(strip.children.map((child) => child.className)).toEqual([
      'vpa-relation-port is-forced is-orientation',
      'vpa-relation-port is-optional is-bound',
    ])
    expect(strip.children.map((child) => child.dataset)).toEqual([
      { portId: 'forced1', portKind: 'forced', portIndex: '0', wire: 'arg1' },
      { portId: 'port1', portKind: 'optional', portIndex: '1', optionalIndex: '0', wire: 'w1' },
    ])
    expect(portStripInsertionIndex(ports, { kind: 'forced' })).toBe(0)
    expect(portStripInsertionIndex(ports, { kind: 'optional', optionalIndex: 0 })).toBe(0)
    expect(portStripInsertionIndex(ports, null)).toBe(1)
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

  it('preserves the previous valid snapshot when an edit candidate is invalid', () => {
    const draft = beginSubstitutionDraft(hostWithBubble(1), 'bubble')
    const before = currentRelationDraft(draft)
    const attempted = editRelationWorkspaceDraft(draft, () => mkDiagram({
      root: before.diagram.root,
      regions: { ...before.diagram.regions },
    }))

    expect(attempted.draft).toBe(draft)
    expect(currentRelationDraft(attempted.draft)).toBe(before)
    expect(attempted.error).toMatch(/missing wire 'arg1'/i)
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

  it('clears pointer claims, highlights, gestures, and mounted state on cancellation', () => {
    let transactionCancelled = 0
    const configured = { ...transaction('abstract'), cancel: () => { transactionCancelled += 1 } }
    const transient: WorkspaceTransientState = {
      pointerClaimed: true,
      draftHoverWire: 'w1',
      hostHoverWire: 'h1',
      connectionGesture: true,
      mounted: true,
    }
    expect(clearRelationWorkspaceTransientState(transient)).toEqual({
      pointerClaimed: false,
      draftHoverWire: null,
      hostHoverWire: null,
      connectionGesture: false,
      mounted: false,
    })
    runRelationWorkspaceCancellation(configured)
    expect(transactionCancelled).toBe(1)
  })
})

describe('substitution transaction', () => {
  it('scratch-checks status and finalizes one labeled proof action with materialized attachments', () => {
    let current = hostWithBubble(1)
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

    current = mkDiagramWithBoundary(current, []).diagram
  })

  it('keeps the workspace open when the kernel or transaction host refuses finalization', () => {
    const source = hostWithBubble(1)
    const snapshot = currentRelationDraft(beginSubstitutionDraft(source, 'bubble'))
    const refusing = transaction('substitute')
    const error = new Error('kernel refused the candidate')
    const result = attemptRelationWorkspaceFinalize({
      ...refusing,
      finalize: () => { throw error },
    }, snapshot, [])

    expect(result).toEqual({ closed: false, error })
  })
})
