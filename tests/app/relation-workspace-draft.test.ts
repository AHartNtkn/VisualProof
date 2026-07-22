import { describe, expect, test } from 'vitest'
import { mkDiagram, type Diagram, type Endpoint, type Wire } from '../../src/kernel/diagram/diagram'
import { bvar, lam } from '../../src/kernel/term/term'
import {
  addRelationRef,
  addRelationTerm,
  applyRelationConnection,
  attachRelationPort,
  beginAbstractionDraft,
  beginSubstitutionDraft,
  bindOptionalPort,
  currentRelationDraft,
  cancelRelationDraft,
  deleteRelationNode,
  deriveRelationExternalReferencePresentation,
  deleteOptionalPort,
  insertOptionalPort,
  materializeRelationDraft,
  materializeRelationSnapshot,
  moveOptionalPort,
  moveRelationHistory,
  planRelationConnection,
  replaceRelationDiagram,
  severRelationEndpoint,
  wrapRelationNode,
  wrapRelationNodes,
  type RelationWorkspaceDraft,
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

function twoTermDiagram(joined = false): Diagram {
  const output = (node: string): Endpoint => ({ node, port: { kind: 'output' } })
  return mkDiagram({
    root: 'r0',
    regions: { r0: { kind: 'sheet' } },
    nodes: {
      n1: { kind: 'term', region: 'r0', term: lam(bvar(0)) },
      n2: { kind: 'term', region: 'r0', term: lam(bvar(0)) },
    },
    wires: joined
      ? { w1: { scope: 'r0', endpoints: [output('n1'), output('n2')] } }
      : {
          w1: { scope: 'r0', endpoints: [output('n1')] },
          w2: { scope: 'r0', endpoints: [output('n2')] },
        },
  })
}

function expectOneSnapshot(before: RelationWorkspaceDraft, after: RelationWorkspaceDraft): void {
  expect(after.history).toHaveLength(before.history.length + 1)
  expect(after.cursor).toBe(before.cursor + 1)
  expect(after.history[after.cursor]).toBe(currentRelationDraft(after))
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
    let draft = withLooseDraftWires(beginSubstitutionDraft(hostWithBubble(0), 'bubble'), ['w1'])
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

  test('substitution and abstraction project snapshots through one canonical materializer', () => {
    let substitution = beginSubstitutionDraft(hostWithBubble(1), 'bubble')
    const subCurrent = currentRelationDraft(substitution)
    substitution = replaceRelationDiagram(substitution, mkDiagram({
      root: subCurrent.diagram.root,
      regions: { ...subCurrent.diagram.regions },
      wires: { ...subCurrent.diagram.wires, parameter: { scope: 'r0', endpoints: [] } },
    }))
    substitution = insertOptionalPort(substitution, 'parameter', 0, 'h1')
    expect(materializeRelationDraft(substitution)).toEqual(
      materializeRelationSnapshot(currentRelationDraft(substitution), 'substitute', substitution.host, 'bubble'),
    )

    let abstraction = withLooseDraftWires(beginAbstractionDraft(hostWithBubble()), ['x'])
    abstraction = insertOptionalPort(abstraction, 'x', 0)
    expect(materializeRelationDraft(abstraction)).toEqual(
      materializeRelationSnapshot(currentRelationDraft(abstraction), 'abstract'),
    )
    expect(() => materializeRelationSnapshot(currentRelationDraft(abstraction), 'substitute'))
      .toThrow(/must be bound or removed/i)
  })

  test('each port mutation is one snapshot and undo/redo restores order and bindings', () => {
    let draft = withLooseDraftWires(beginSubstitutionDraft(hostWithBubble(0), 'bubble'), ['w1', 'w2'])
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

  test('diagram replacement commits the complete diagram and retained ports in one snapshot', () => {
    const draft = beginSubstitutionDraft(hostWithBubble(1), 'bubble')
    const replacement = mkDiagram({
      root: 'r0',
      regions: { r0: { kind: 'sheet' } },
      nodes: { n1: { kind: 'term', region: 'r0', term: lam(bvar(0)) } },
      wires: {
        arg1: { scope: 'r0', endpoints: [] },
        result: { scope: 'r0', endpoints: [{ node: 'n1', port: { kind: 'output' } }] },
      },
    })

    const replaced = replaceRelationDiagram(draft, replacement)

    expectOneSnapshot(draft, replaced)
    expect(currentRelationDraft(replaced)).toMatchObject({
      diagram: replacement,
      ports: [{ id: 'forced1', wire: 'arg1', kind: 'forced' }],
    })
    expect(currentRelationDraft(replaced).comprehension?.pattern.diagram).toEqual(replacement)
    expect(currentRelationDraft(draft).diagram.nodes).toEqual({})
  })

  test('substitution connection preview is pure and connection commit applies its checked host binding atomically', () => {
    const draft = withLooseDraftWires(beginSubstitutionDraft(hostWithBubble(0), 'bubble'), ['w1'])
    const before = currentRelationDraft(draft)

    const preview = planRelationConnection(
      draft,
      { kind: 'draft', wire: 'w1' },
      { kind: 'host', wire: 'h1' },
    )

    expect(preview).toMatchObject({
      ok: true,
      kind: 'external-reference',
      snapshot: { ports: [{ wire: 'w1', kind: 'optional', hostWire: 'h1' }] },
    })
    expect(draft.history).toHaveLength(2)
    expect(currentRelationDraft(draft)).toBe(before)

    const committed = applyRelationConnection(
      draft,
      { kind: 'draft', wire: 'w1' },
      { kind: 'host', wire: 'h1' },
    )
    expectOneSnapshot(draft, committed)
    expect(currentRelationDraft(committed)).toEqual(preview.ok ? preview.snapshot : null)
    expect(currentRelationDraft(committed).diagram).toBe(before.diagram)
  })

  test('abstraction refuses host bindings before they can enter a draft snapshot', () => {
    const draft = withLooseDraftWires(beginAbstractionDraft(hostWithBubble()), ['w1'])
    const before = currentRelationDraft(draft)

    expect(planRelationConnection(
      draft,
      { kind: 'draft', wire: 'w1' },
      { kind: 'host', wire: 'h1' },
    )).toMatchObject({ ok: false, code: 'host-binding-unavailable' })
    expect(() => applyRelationConnection(
      draft,
      { kind: 'host', wire: 'h1' },
      { kind: 'draft', wire: 'w1' },
    )).toThrow(/host bindings.*substitution/i)
    expect(() => insertOptionalPort(draft, 'w1', 0, 'h1')).toThrow(/host bindings.*substitution/i)
    expect(() => materializeRelationSnapshot({
      ...before,
      ports: [{ id: 'invalid-host-binding', wire: 'w1', kind: 'optional', hostWire: 'h1' }],
    }, 'abstract')).toThrow(/host bindings.*substitution/i)
    expect(draft.history).toHaveLength(2)
    expect(currentRelationDraft(draft)).toBe(before)

    const boundaryOnly = insertOptionalPort(draft, 'w1', 0)
    expect(currentRelationDraft(boundaryOnly).ports).toEqual([
      expect.objectContaining({ wire: 'w1', kind: 'optional' }),
    ])
    expect(currentRelationDraft(boundaryOnly).ports[0]).not.toHaveProperty('hostWire')
  })

  test('refused connection previews and commits add no snapshot', () => {
    let draft = withLooseDraftWires(beginSubstitutionDraft(hostWithBubble(0), 'bubble'), ['w1'])
    draft = applyRelationConnection(
      draft,
      { kind: 'draft', wire: 'w1' },
      { kind: 'host', wire: 'h1' },
    )
    const length = draft.history.length
    const before = currentRelationDraft(draft)

    expect(planRelationConnection(
      draft,
      { kind: 'draft', wire: 'w1' },
      { kind: 'host', wire: 'h1' },
    )).toMatchObject({ ok: false, code: 'duplicate-external-reference' })
    expect(() => applyRelationConnection(
      draft,
      { kind: 'draft', wire: 'w1' },
      { kind: 'host', wire: 'h1' },
    )).toThrow(/already exists/i)
    expect(draft.history).toHaveLength(length)
    expect(currentRelationDraft(draft)).toBe(before)
  })

  test('spawning a term commits its node and complete port wiring in one snapshot', () => {
    const draft = beginAbstractionDraft(hostWithBubble())

    const spawned = addRelationTerm(draft, lam(bvar(0)))

    expectOneSnapshot(draft, spawned)
    expect(Object.values(currentRelationDraft(spawned).diagram.nodes)).toEqual([
      { kind: 'term', region: 'r0', term: lam(bvar(0)), freePorts: [] },
    ])
    expect(Object.values(currentRelationDraft(spawned).diagram.wires)).toEqual([
      { scope: 'r0', endpoints: [{ node: 'n', port: { kind: 'output' } }] },
    ])
    expect(currentRelationDraft(spawned).ports).toEqual([])
  })

  test('spawning a named relation commits its arity and argument wiring in one snapshot', () => {
    const draft = beginAbstractionDraft(hostWithBubble())

    const spawned = addRelationRef(draft, 'named-relation', 2)

    expectOneSnapshot(draft, spawned)
    expect(Object.values(currentRelationDraft(spawned).diagram.nodes)).toEqual([
      { kind: 'ref', region: 'r0', defId: 'named-relation', arity: 2 },
    ])
    expect(Object.values(currentRelationDraft(spawned).diagram.wires)).toEqual([
      { scope: 'r0', endpoints: [{ node: 'n', port: { kind: 'arg', index: 0 } }] },
      { scope: 'r0', endpoints: [{ node: 'n', port: { kind: 'arg', index: 1 } }] },
    ])
    expect(currentRelationDraft(spawned).ports).toEqual([])
  })

  test('local attachment fuses wire topology and rewrites its port in one snapshot', () => {
    let draft = replaceRelationDiagram(beginSubstitutionDraft(hostWithBubble(0), 'bubble'), twoTermDiagram())
    draft = insertOptionalPort(draft, 'w2', 0, 'h1')
    const port = currentRelationDraft(draft).ports[0]!

    const attached = attachRelationPort(draft, port.id, 'w1')

    expectOneSnapshot(draft, attached)
    expect(Object.keys(currentRelationDraft(attached).diagram.wires)).toEqual(['w2'])
    expect(currentRelationDraft(attached).diagram.wires.w2!.endpoints).toEqual([
      { node: 'n1', port: { kind: 'output' } },
      { node: 'n2', port: { kind: 'output' } },
    ])
    expect(currentRelationDraft(attached).ports).toEqual([
      { id: port.id, wire: 'w2', kind: 'optional', hostWire: 'h1' },
    ])
  })

  test('attaching a port to its existing identity is a no-op with no snapshot', () => {
    let draft = withLooseDraftWires(beginAbstractionDraft(hostWithBubble()), ['w1'])
    draft = insertOptionalPort(draft, 'w1', 0)
    const port = currentRelationDraft(draft).ports[0]!

    const unchanged = attachRelationPort(draft, port.id, 'w1')

    expect(unchanged).toBe(draft)
    expect(unchanged.history).toHaveLength(draft.history.length)
    expect(currentRelationDraft(unchanged)).toEqual(currentRelationDraft(draft))
  })

  test('node deletion retains a bound interface wire and commits one complete snapshot', () => {
    let draft = replaceRelationDiagram(beginSubstitutionDraft(hostWithBubble(0), 'bubble'), twoTermDiagram())
    draft = insertOptionalPort(draft, 'w1', 0, 'h1')
    const before = currentRelationDraft(draft)

    const deleted = deleteRelationNode(draft, 'n1')

    expectOneSnapshot(draft, deleted)
    expect(currentRelationDraft(deleted).diagram.nodes).toEqual({ n2: before.diagram.nodes.n2 })
    expect(currentRelationDraft(deleted).diagram.wires).toEqual({
      w1: { scope: 'r0', endpoints: [] },
      w2: before.diagram.wires.w2,
    })
    expect(currentRelationDraft(deleted).ports).toEqual(before.ports)
  })

  test('wrapping a node in a cut moves its node and wire under one new boundary snapshot', () => {
    const draft = replaceRelationDiagram(beginAbstractionDraft(hostWithBubble()), twoTermDiagram())

    const wrapped = wrapRelationNode(draft, 'n1')

    expectOneSnapshot(draft, wrapped)
    expect(currentRelationDraft(wrapped).diagram.regions).toEqual({
      r0: { kind: 'sheet' },
      cut: { kind: 'cut', parent: 'r0' },
    })
    expect(currentRelationDraft(wrapped).diagram.nodes.n1).toMatchObject({ region: 'cut' })
    expect(currentRelationDraft(wrapped).diagram.wires.w1).toMatchObject({ scope: 'cut' })
    expect(currentRelationDraft(wrapped).ports).toEqual([])
  })

  test('wrapping nodes in a bubble records arity and moves the selected contents in one snapshot', () => {
    const draft = replaceRelationDiagram(beginAbstractionDraft(hostWithBubble()), twoTermDiagram())

    const wrapped = wrapRelationNodes(draft, ['n1', 'n2'], 3)

    expectOneSnapshot(draft, wrapped)
    expect(currentRelationDraft(wrapped).diagram.regions).toEqual({
      r0: { kind: 'sheet' },
      bub: { kind: 'bubble', parent: 'r0', arity: 3 },
    })
    expect(Object.values(currentRelationDraft(wrapped).diagram.nodes).map((node) => node.region)).toEqual(['bub', 'bub'])
    expect(Object.values(currentRelationDraft(wrapped).diagram.wires).map((wire) => wire.scope)).toEqual(['bub', 'bub'])
    expect(currentRelationDraft(wrapped).ports).toEqual([])
  })

  test('endpoint severing splits one incidence onto a fresh wire in one snapshot', () => {
    const draft = replaceRelationDiagram(beginAbstractionDraft(hostWithBubble()), twoTermDiagram(true))
    const endpoint = { node: 'n1', port: { kind: 'output' as const } }

    const severed = severRelationEndpoint(draft, 'w1', endpoint)

    expectOneSnapshot(draft, severed)
    expect(currentRelationDraft(severed).diagram.wires).toEqual({
      w1: { scope: 'r0', endpoints: [{ node: 'n2', port: { kind: 'output' } }] },
      w: { scope: 'r0', endpoints: [endpoint] },
    })
    expect(currentRelationDraft(severed).ports).toEqual([])
  })

  test('refused endpoint severing leaves diagram, ports, and history unchanged', () => {
    const draft = replaceRelationDiagram(beginAbstractionDraft(hostWithBubble()), twoTermDiagram(true))
    const severed = severRelationEndpoint(draft, 'w1', { node: 'n1', port: { kind: 'output' } })
    const before = currentRelationDraft(severed)

    expect(() => severRelationEndpoint(
      severed,
      'w',
      { node: 'n1', port: { kind: 'output' } },
    )).toThrow(/single loose end/i)
    expect(severed.history).toHaveLength(draft.history.length + 1)
    expect(currentRelationDraft(severed)).toBe(before)
  })

  test('undo and redo restore fused diagram topology together with bound ports', () => {
    let draft = replaceRelationDiagram(beginSubstitutionDraft(hostWithBubble(0), 'bubble'), twoTermDiagram())
    draft = insertOptionalPort(draft, 'w1', 0, 'h1')
    draft = insertOptionalPort(draft, 'w2', 1, 'h2')
    const beforeFusion = currentRelationDraft(draft)
    const firstPort = beforeFusion.ports[0]!

    const fused = attachRelationPort(draft, firstPort.id, 'w2')
    const fusedSnapshot = currentRelationDraft(fused)
    expectOneSnapshot(draft, fused)
    expect(Object.keys(fusedSnapshot.diagram.wires)).toEqual(['w1'])
    expect(fusedSnapshot.ports).toEqual([
      expect.objectContaining({ wire: 'w1', hostWire: 'h1' }),
      expect.objectContaining({ wire: 'w1', hostWire: 'h2' }),
    ])

    const undone = moveRelationHistory(fused, -1)
    expect(currentRelationDraft(undone)).toBe(beforeFusion)
    expect(Object.keys(currentRelationDraft(undone).diagram.wires)).toEqual(['w1', 'w2'])
    expect(currentRelationDraft(undone).ports).toEqual([
      expect.objectContaining({ wire: 'w1', hostWire: 'h1' }),
      expect.objectContaining({ wire: 'w2', hostWire: 'h2' }),
    ])

    const redone = moveRelationHistory(undone, 1)
    expect(currentRelationDraft(redone)).toBe(fusedSnapshot)
    expect(currentRelationDraft(redone).diagram).toEqual(fusedSnapshot.diagram)
    expect(currentRelationDraft(redone).ports).toEqual(fusedSnapshot.ports)
  })

  test('plans the same local quotient regardless of connection gesture direction', () => {
    const draft = replaceRelationDiagram(beginAbstractionDraft(hostWithBubble()), twoTermDiagram())
    const left = planRelationConnection(draft, { kind: 'draft', wire: 'w1' }, { kind: 'draft', wire: 'w2' })
    const right = planRelationConnection(draft, { kind: 'draft', wire: 'w2' }, { kind: 'draft', wire: 'w1' })

    expect(left.ok && left.snapshot).toEqual(right.ok && right.snapshot)
  })

  test('plans external references symmetrically and refuses host-only connections', () => {
    const draft = withLooseDraftWires(beginSubstitutionDraft(hostWithBubble(0), 'bubble'), ['w1'])
    const draftFirst = planRelationConnection(draft, { kind: 'draft', wire: 'w1' }, { kind: 'host', wire: 'h1' })
    const hostFirst = planRelationConnection(draft, { kind: 'host', wire: 'h1' }, { kind: 'draft', wire: 'w1' })

    expect(draftFirst).toEqual(hostFirst)
    expect(planRelationConnection(draft, { kind: 'host', wire: 'h1' }, { kind: 'host', wire: 'h2' }))
      .toMatchObject({ ok: false, code: 'host-to-host' })
  })

  test('marks only real host bindings and propagates their active glow', () => {
    const ports = [
      { id: 'port1', wire: 'w1', kind: 'optional' as const, hostWire: 'h1' },
      { id: 'port2', wire: 'w2', kind: 'optional' as const },
    ]

    const presentation = deriveRelationExternalReferencePresentation(ports, new Set(), new Set(['h1', 'h2']))

    expect([...presentation.markedDraft]).toEqual(['w1'])
    expect([...presentation.markedHost]).toEqual(['h1'])
    expect([...presentation.glowingDraft]).toEqual(['w1'])
    expect([...presentation.glowingHost]).toEqual(['h1'])
  })

  test('cancels by returning the exact immutable host snapshot', () => {
    const host = hostWithBubble()
    const draft = beginSubstitutionDraft(host, 'bubble')

    expect(cancelRelationDraft(draft)).toBe(host)
  })
})
