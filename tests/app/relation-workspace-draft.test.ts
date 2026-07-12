import { describe, expect, test } from 'vitest'
import { mkDiagram, type Diagram, type Wire } from '../../src/kernel/diagram/diagram'
import {
  beginAbstractionDraft,
  beginSubstitutionDraft,
  bindOptionalPort,
  currentRelationDraft,
  deleteOptionalPort,
  insertOptionalPort,
  materializeRelationDraft,
  moveOptionalPort,
  moveRelationHistory,
  replaceRelationDiagram,
} from '../../src/app/relation-workspace-draft'

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
      h3: { scope: 'r0', endpoints: [] },
    },
  })
}

function withLooseDraftWires(draft: ReturnType<typeof beginAbstractionDraft>, ids: readonly string[]) {
  const wires: Record<string, Wire> = Object.fromEntries(
    ids.map((id) => [id, { scope: 'r0', endpoints: [] }]),
  )
  return replaceRelationDiagram(draft, mkDiagram({
    root: 'r0',
    regions: { r0: { kind: 'sheet' } },
    wires,
  }))
}

describe('relation workspace port model', () => {
  test('substitution starts with a locked ordered forced block matching the target arity', () => {
    const draft = beginSubstitutionDraft(hostWithBubble(3), 'bubble')
    const ports = currentRelationDraft(draft).ports

    expect(ports.map(({ wire, kind }) => ({ wire, kind }))).toEqual([
      { wire: 'arg1', kind: 'forced' },
      { wire: 'arg2', kind: 'forced' },
      { wire: 'arg3', kind: 'forced' },
    ])
    expect(() => moveOptionalPort(draft, ports[1]!.id, 0)).toThrow(/forced port.*cannot be moved/i)
    expect(() => deleteOptionalPort(draft, ports[1]!.id)).toThrow(/forced port.*cannot be deleted/i)
  })

  test('abstraction starts with no ports', () => {
    const draft = beginAbstractionDraft(hostWithBubble())

    expect(currentRelationDraft(draft).ports).toEqual([])
    expect(materializeRelationDraft(draft).relation.boundary).toEqual([])
  })

  test('inserting a draft wire at an optional strip index preserves that spatial position', () => {
    let draft = withLooseDraftWires(beginAbstractionDraft(hostWithBubble()), ['w1', 'w2', 'w3'])
    draft = insertOptionalPort(draft, 'w1', 0)
    draft = insertOptionalPort(draft, 'w3', 1)
    draft = insertOptionalPort(draft, 'w2', 1)

    expect(currentRelationDraft(draft).ports.map((port) => port.wire)).toEqual(['w1', 'w2', 'w3'])
  })

  test('optional ports reorder within the optional strip', () => {
    let draft = withLooseDraftWires(beginAbstractionDraft(hostWithBubble()), ['w1', 'w2', 'w3'])
    draft = insertOptionalPort(draft, 'w1', 0)
    draft = insertOptionalPort(draft, 'w2', 1)
    draft = insertOptionalPort(draft, 'w3', 2)
    const first = currentRelationDraft(draft).ports[0]!

    draft = moveOptionalPort(draft, first.id, 2)

    expect(currentRelationDraft(draft).ports.map((port) => port.wire)).toEqual(['w2', 'w3', 'w1'])
  })

  test('deleting an optional port removes its pending host binding', () => {
    let draft = withLooseDraftWires(beginAbstractionDraft(hostWithBubble()), ['w1'])
    draft = insertOptionalPort(draft, 'w1', 0, 'h1')
    const port = currentRelationDraft(draft).ports[0]!

    draft = deleteOptionalPort(draft, port.id)

    expect(currentRelationDraft(draft).ports).toEqual([])
    expect(materializeRelationDraft(draft).attachments).toEqual([])
  })

  test('an optional substitution parameter must be bound or removed before materialization', () => {
    let draft = beginSubstitutionDraft(hostWithBubble(1), 'bubble')
    const current = currentRelationDraft(draft)
    const diagram = mkDiagram({
      root: current.diagram.root,
      regions: { ...current.diagram.regions },
      nodes: { ...current.diagram.nodes },
      wires: { ...current.diagram.wires, extra: { scope: 'r0', endpoints: [] } },
    })
    draft = replaceRelationDiagram(draft, diagram)
    draft = insertOptionalPort(draft, 'extra', 0)
    const optional = currentRelationDraft(draft).ports[1]!

    expect(() => materializeRelationDraft(draft)).toThrow(/optional substitution port.*must be bound or removed/i)

    const bound = bindOptionalPort(draft, optional.id, 'h2')
    expect(materializeRelationDraft(bound)).toMatchObject({ attachments: ['h2'] })

    const removed = deleteOptionalPort(draft, optional.id)
    expect(materializeRelationDraft(removed)).toMatchObject({ attachments: [] })
  })

  test('abstraction boundary order and arity come from the submitted strip', () => {
    let draft = withLooseDraftWires(beginAbstractionDraft(hostWithBubble()), ['x', 'y'])
    draft = insertOptionalPort(draft, 'y', 0)
    draft = insertOptionalPort(draft, 'x', 0)

    const materialized = materializeRelationDraft(draft)

    expect(materialized.relation.boundary).toEqual(['x', 'y'])
    expect(materialized.relation.boundary).toHaveLength(2)
  })

  test('each port mutation is one snapshot and undo/redo restores order and bindings', () => {
    let draft = withLooseDraftWires(beginAbstractionDraft(hostWithBubble()), ['w1', 'w2'])
    const initialLength = draft.history.length

    draft = insertOptionalPort(draft, 'w1', 0, 'h1')
    expect(draft.history).toHaveLength(initialLength + 1)
    const w1 = currentRelationDraft(draft).ports[0]!

    draft = insertOptionalPort(draft, 'w2', 1)
    expect(draft.history).toHaveLength(initialLength + 2)
    const w2 = currentRelationDraft(draft).ports[1]!

    draft = moveOptionalPort(draft, w2.id, 0)
    expect(draft.history).toHaveLength(initialLength + 3)

    draft = bindOptionalPort(draft, w2.id, 'h2')
    expect(draft.history).toHaveLength(initialLength + 4)

    draft = deleteOptionalPort(draft, w1.id)
    expect(draft.history).toHaveLength(initialLength + 5)
    expect(currentRelationDraft(draft).ports).toEqual([
      expect.objectContaining({ id: w2.id, wire: 'w2', hostWire: 'h2' }),
    ])

    draft = moveRelationHistory(draft, -1)
    expect(currentRelationDraft(draft).ports).toEqual([
      expect.objectContaining({ id: w2.id, wire: 'w2', hostWire: 'h2' }),
      expect.objectContaining({ id: w1.id, wire: 'w1', hostWire: 'h1' }),
    ])

    draft = moveRelationHistory(draft, -1)
    expect(currentRelationDraft(draft).ports[0]).not.toHaveProperty('hostWire')

    draft = moveRelationHistory(draft, 2)
    expect(currentRelationDraft(draft).ports).toEqual([
      expect.objectContaining({ id: w2.id, wire: 'w2', hostWire: 'h2' }),
    ])
  })
})
