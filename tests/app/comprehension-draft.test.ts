import { describe, expect, it } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { mkDiagram } from '../../src/kernel/diagram/diagram'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import {
  addComprehensionTerm,
  applyComprehensionConnection,
  attachComprehensionSocket,
  beginComprehensionDraft,
  cancelComprehensionDraft,
  commitComprehensionDraft,
  currentComprehensionDraft,
  deleteComprehensionNode,
  deriveExternalReferencePresentation,
  materializeComprehensionSnapshot,
  moveComprehensionHistory,
  planComprehensionConnection,
  replaceComprehensionDiagram,
  ungraftComprehensionWire,
} from '../../src/app/comprehension-draft'
import { comprehensionFixture } from './comprehension-fixture'

const draftWire = (wire: string) => ({ kind: 'draft' as const, wire })
const hostWire = (wire: string) => ({ kind: 'host' as const, wire })

function draftWithConstant() {
  const fixture = comprehensionFixture()
  const draft = addComprehensionTerm(beginComprehensionDraft(fixture.diagram, fixture.bubble), parseTerm('a'))
  const relation = currentComprehensionDraft(draft).relation
  const wire = Object.keys(relation.diagram.wires).find((id) => !relation.boundary.includes(id))!
  const node = Object.keys(relation.diagram.nodes)[0]!
  return { fixture, draft, wire, node }
}

describe('anonymous comprehension draft transaction', () => {
  it('accepts a validated whole-diagram edit while preserving formal positions', () => {
    const { draft, node } = draftWithConstant()
    const current = currentComprehensionDraft(draft)
    const edited = mkDiagram({
      root: current.relation.diagram.root,
      regions: { ...current.relation.diagram.regions, r1: { kind: 'cut', parent: current.relation.diagram.root } },
      nodes: { ...current.relation.diagram.nodes, [node]: { ...current.relation.diagram.nodes[node]!, region: 'r1' } },
      wires: { ...current.relation.diagram.wires },
    })

    const changed = replaceComprehensionDiagram(draft, edited)
    expect(currentComprehensionDraft(changed).relation.boundary).toEqual(['arg1', 'arg2'])
    expect(changed.history).toHaveLength(draft.history.length + 1)
    expect(currentComprehensionDraft(changed).relation.diagram.nodes[node]!.region).toBe('r1')
  })

  it('drops an external binding only when its non-formal draft identity disappears', () => {
    const { fixture, draft, wire } = draftWithConstant()
    const grafted = applyComprehensionConnection(draft, draftWire(wire), hostWire(fixture.parameter))
    const current = currentComprehensionDraft(grafted)
    const edited = mkDiagram({
      root: current.relation.diagram.root,
      regions: { ...current.relation.diagram.regions },
      nodes: {},
      wires: {
        arg1: current.relation.diagram.wires.arg1!,
        arg2: current.relation.diagram.wires.arg2!,
      },
    })

    const changed = replaceComprehensionDiagram(grafted, edited)
    expect(currentComprehensionDraft(changed).externalWires).toEqual([])
    expect(currentComprehensionDraft(changed).relation.boundary).toEqual(['arg1', 'arg2'])
  })

  it('refuses deletion of a formal position and invalid external scope without appending history', () => {
    const fixture = comprehensionFixture()
    const draft = beginComprehensionDraft(fixture.diagram, fixture.bubble)
    const current = currentComprehensionDraft(draft)
    const missingFormal = mkDiagram({
      root: current.relation.diagram.root,
      regions: { ...current.relation.diagram.regions },
      nodes: { ...current.relation.diagram.nodes },
      wires: { arg1: current.relation.diagram.wires.arg1! },
    })
    expect(() => replaceComprehensionDiagram(draft, missingFormal)).toThrow(/formal boundary wire 'arg2' cannot be removed/)
    expect(draft.history).toHaveLength(1)

    const grafted = applyComprehensionConnection(draft, draftWire('arg1'), hostWire(fixture.parameter))
    const withCut = mkDiagram({
      root: current.relation.diagram.root,
      regions: { ...current.relation.diagram.regions, r1: { kind: 'cut', parent: current.relation.diagram.root } },
      nodes: { ...current.relation.diagram.nodes },
      wires: {
        ...current.relation.diagram.wires,
        arg1: { ...current.relation.diagram.wires.arg1!, scope: 'r1' },
      },
    })
    expect(() => replaceComprehensionDiagram(grafted, withCut)).toThrow(/not root-scoped/)
    expect(grafted.history).toHaveLength(2)
  })

  it('owns stable ordered formal positions and permits a diagonal wire between boundary ports', () => {
    const { draft, wire } = draftWithConstant()
    const joined = attachComprehensionSocket(draft, 1, wire)
    expect(currentComprehensionDraft(joined).relation.boundary).toEqual(['arg1', 'arg2'])
    expect(currentComprehensionDraft(joined).relation.diagram.wires.arg2!.endpoints).toHaveLength(1)
    const diagonal = applyComprehensionConnection(joined, draftWire('arg1'), draftWire('arg2'))
    expect(currentComprehensionDraft(diagonal).relation.boundary).toEqual(['arg1', 'arg1'])
    expect(currentComprehensionDraft(diagonal).relation.diagram.wires.arg2).toBeUndefined()
    expect(currentComprehensionDraft(diagonal).relation.diagram.wires.arg1!.endpoints).toHaveLength(1)
    expect(() => commitComprehensionDraft(diagonal)).not.toThrow()
    const undone = moveComprehensionHistory(diagonal, -1)
    expect(currentComprehensionDraft(undone).relation.boundary).toEqual(['arg1', 'arg2'])
    expect(currentComprehensionDraft(moveComprehensionHistory(undone, 1)).relation.boundary).toEqual(['arg1', 'arg1'])
  })

  it('plans the same local quotient regardless of gesture direction', () => {
    const fixture = comprehensionFixture()
    const draft = beginComprehensionDraft(fixture.diagram, fixture.bubble)
    const forward = planComprehensionConnection(draft, draftWire('arg1'), draftWire('arg2'))
    const reverse = planComprehensionConnection(draft, draftWire('arg2'), draftWire('arg1'))
    expect(forward.ok).toBe(true)
    expect(reverse.ok).toBe(true)
    expect(forward.ok && reverse.ok ? forward.snapshot : null)
      .toEqual(forward.ok && reverse.ok ? reverse.snapshot : null)
  })

  it('plans and commits the same external reference from either surface', () => {
    const fixture = comprehensionFixture()
    const draft = beginComprehensionDraft(fixture.diagram, fixture.bubble)
    const fromDraft = planComprehensionConnection(draft, draftWire('arg1'), hostWire(fixture.parameter))
    const fromHost = planComprehensionConnection(draft, hostWire(fixture.parameter), draftWire('arg1'))

    expect(fromHost).toEqual(fromDraft)
    expect(currentComprehensionDraft(applyComprehensionConnection(
      draft,
      hostWire(fixture.parameter),
      draftWire('arg1'),
    ))).toEqual(currentComprehensionDraft(applyComprehensionConnection(
      draft,
      draftWire('arg1'),
      hostWire(fixture.parameter),
    )))
  })

  it('refuses a connection entirely within the read-only host', () => {
    const fixture = comprehensionFixture()
    const draft = beginComprehensionDraft(fixture.diagram, fixture.bubble)
    expect(planComprehensionConnection(
      draft,
      hostWire(fixture.parameter),
      hostWire(fixture.parameter),
    )).toMatchObject({ ok: false, code: 'host-to-host' })
  })

  it('canonicalizes endpoint order across equivalent multi-step fusions', () => {
    const fixture = comprehensionFixture()
    let draft = addComprehensionTerm(beginComprehensionDraft(fixture.diagram, fixture.bubble), parseTerm('a'))
    draft = addComprehensionTerm(draft, parseTerm('b'))
    const [a, b, c] = Object.keys(currentComprehensionDraft(draft).relation.diagram.wires)
      .filter((wire) => !wire.startsWith('arg'))
      .sort()
    expect([a, b, c].every((wire) => wire !== undefined)).toBe(true)

    const leftFirst = applyComprehensionConnection(draft, draftWire(b!), draftWire(c!))
    const left = applyComprehensionConnection(leftFirst, draftWire(a!), draftWire(b!))
    const rightFirst = applyComprehensionConnection(draft, draftWire(a!), draftWire(c!))
    const right = applyComprehensionConnection(rightFirst, draftWire(a!), draftWire(b!))

    expect(currentComprehensionDraft(left)).toEqual(currentComprehensionDraft(right))
  })

  it('reuses one imported port by fusing a second draft wire connected to the same host', () => {
    const fixture = comprehensionFixture()
    const start = beginComprehensionDraft(fixture.diagram, fixture.bubble)
    const first = applyComprehensionConnection(start, hostWire(fixture.parameter), draftWire('arg1'))
    const fromDraft = planComprehensionConnection(first, draftWire('arg2'), hostWire(fixture.parameter))
    const fromHost = planComprehensionConnection(first, hostWire(fixture.parameter), draftWire('arg2'))
    expect(fromHost).toEqual(fromDraft)
    expect(fromHost).toMatchObject({ ok: true, kind: 'local-fusion' })

    const merged = applyComprehensionConnection(first, hostWire(fixture.parameter), draftWire('arg2'))
    const current = currentComprehensionDraft(merged)
    expect(current.relation.boundary).toEqual(['arg1', 'arg1'])
    expect(current.relation.diagram.wires.arg2).toBeUndefined()
    expect(current.externalWires).toEqual([{ draftWire: 'arg1', hostWire: fixture.parameter }])
    const materialized = materializeComprehensionSnapshot(current)
    expect(materialized.relation.boundary).toEqual(['arg1', 'arg1', 'arg1'])
    expect(materialized.attachments).toEqual([fixture.parameter])
    expect(() => commitComprehensionDraft(merged)).not.toThrow()

    expect(currentComprehensionDraft(moveComprehensionHistory(merged, -1))).toEqual(currentComprehensionDraft(first))
    expect(currentComprehensionDraft(moveComprehensionHistory(moveComprehensionHistory(merged, -1), 1))).toEqual(current)
  })

  it('rejects a snapshot that gives one host more than one draft representative', () => {
    const fixture = comprehensionFixture()
    const draft = beginComprehensionDraft(fixture.diagram, fixture.bubble)
    const current = currentComprehensionDraft(draft)
    const corrupted = {
      ...draft,
      history: [{
        relation: current.relation,
        externalWires: [
          { draftWire: 'arg1', hostWire: fixture.parameter },
          { draftWire: 'arg2', hostWire: fixture.parameter },
        ],
      }],
    }
    expect(() => planComprehensionConnection(corrupted, draftWire('arg1'), hostWire(fixture.parameter)))
      .toThrow(`external host wire '${fixture.parameter}' has more than one draft representative`)
  })

  it('allows a formal boundary identity to reference a host without changing the stored formal interface', () => {
    const fixture = comprehensionFixture()
    const draft = beginComprehensionDraft(fixture.diagram, fixture.bubble)
    const plan = planComprehensionConnection(draft, draftWire('arg1'), hostWire(fixture.parameter))
    expect(plan.ok).toBe(true)
    const grafted = applyComprehensionConnection(draft, draftWire('arg1'), hostWire(fixture.parameter))
    const current = currentComprehensionDraft(grafted)
    expect(current.relation.boundary).toEqual(['arg1', 'arg2'])
    expect(current.externalWires).toEqual([{ draftWire: 'arg1', hostWire: fixture.parameter }])
    const materialized = materializeComprehensionSnapshot(current)
    expect(materialized.relation.boundary).toEqual(['arg1', 'arg2', 'arg1'])
    expect(materialized.attachments).toEqual([fixture.parameter])
    expect(() => commitComprehensionDraft(grafted)).not.toThrow()
  })

  it('lets a wire already attached to a formal boundary position reference a host', () => {
    const { fixture, draft, wire } = draftWithConstant()
    const attached = applyComprehensionConnection(draft, draftWire('arg2'), draftWire(wire))
    expect(currentComprehensionDraft(attached).relation.diagram.wires.arg2!.endpoints).toHaveLength(1)
    const fromDraft = planComprehensionConnection(attached, draftWire('arg2'), hostWire(fixture.parameter))
    const fromHost = planComprehensionConnection(attached, hostWire(fixture.parameter), draftWire('arg2'))
    expect(fromDraft.ok).toBe(true)
    expect(fromHost).toEqual(fromDraft)
    const grafted = applyComprehensionConnection(attached, draftWire('arg2'), hostWire(fixture.parameter))
    expect(currentComprehensionDraft(grafted).relation.boundary).toEqual(['arg1', 'arg2'])
    expect(currentComprehensionDraft(grafted).externalWires).toEqual([{ draftWire: 'arg2', hostWire: fixture.parameter }])
    expect(materializeComprehensionSnapshot(currentComprehensionDraft(grafted)).relation.boundary).toEqual(['arg1', 'arg2', 'arg2'])

    const ungrafted = ungraftComprehensionWire(grafted, 'arg2')
    expect(currentComprehensionDraft(ungrafted).relation.boundary).toEqual(['arg1', 'arg2'])
    expect(currentComprehensionDraft(ungrafted).relation.diagram.wires.arg2!.endpoints).toHaveLength(1)
    expect(currentComprehensionDraft(ungrafted).externalWires).toEqual([])
  })

  it('uses the same checked plan for preview and history commit', () => {
    const { fixture, draft, wire } = draftWithConstant()
    const plan = planComprehensionConnection(draft, draftWire(wire), hostWire(fixture.parameter))
    expect(plan.ok).toBe(true)
    const committed = applyComprehensionConnection(draft, draftWire(wire), hostWire(fixture.parameter))
    expect(currentComprehensionDraft(committed)).toEqual(plan.ok ? plan.snapshot : null)
    expect(committed.history).toHaveLength(draft.history.length + 1)
  })

  it('refuses exact duplicate references and same-identity local connections without adding history', () => {
    const { fixture, draft, wire } = draftWithConstant()
    const grafted = applyComprehensionConnection(draft, draftWire(wire), hostWire(fixture.parameter))
    expect(planComprehensionConnection(grafted, draftWire(wire), hostWire(fixture.parameter))).toMatchObject({
      ok: false, code: 'duplicate-external-reference',
    })
    expect(planComprehensionConnection(grafted, draftWire(wire), draftWire(wire))).toMatchObject({
      ok: false, code: 'same-local-identity',
    })
    expect(() => applyComprehensionConnection(grafted, draftWire(wire), hostWire(fixture.parameter))).toThrow('already exists')
    expect(grafted.history).toHaveLength(draft.history.length + 1)
  })

  it('allows a nested wire as a local source but refuses it as an external source', () => {
    const fixture = comprehensionFixture()
    const base = beginComprehensionDraft(fixture.diagram, fixture.bubble)
    const current = currentComprehensionDraft(base)
    const nested = mkDiagram({
      root: current.relation.diagram.root,
      regions: {
        ...current.relation.diagram.regions,
        nested: { kind: 'cut', parent: current.relation.diagram.root },
      },
      nodes: {
        nestedNode: { kind: 'term', region: 'nested', term: parseTerm('\\x. x') },
      },
      wires: {
        ...current.relation.diagram.wires,
        nestedWire: {
          scope: 'nested',
          endpoints: [{ node: 'nestedNode', port: { kind: 'output' } }],
        },
      },
    })
    const draft = {
      ...base,
      history: [{ relation: mkDiagramWithBoundary(nested, current.relation.boundary), externalWires: [] }],
    }
    expect(planComprehensionConnection(draft, draftWire('nestedWire'), hostWire(fixture.parameter))).toMatchObject({
      ok: false, code: 'non-root-external-source',
    })
    expect(planComprehensionConnection(draft, hostWire(fixture.parameter), draftWire('nestedWire'))).toMatchObject({
      ok: false, code: 'non-root-external-source',
    })
    const imported = applyComprehensionConnection(draft, draftWire('arg1'), hostWire(fixture.parameter))
    expect(planComprehensionConnection(imported, hostWire(fixture.parameter), draftWire('nestedWire'))).toMatchObject({
      ok: false, code: 'non-root-external-source',
    })
    expect(planComprehensionConnection(draft, draftWire('nestedWire'), draftWire('arg1')).ok).toBe(true)
  })

  it('propagates structural failures instead of disguising them as ineligibility', () => {
    const { draft, wire } = draftWithConstant()
    const corrupted = { ...draft, bubble: 'missing-bubble' }
    expect(() => planComprehensionConnection(corrupted, draftWire(wire), hostWire('ghost'))).toThrow("unknown region 'missing-bubble'")
  })

  it('derives the same connection matrix after cancel and reopen', () => {
    const fixture = comprehensionFixture()
    const opened = beginComprehensionDraft(fixture.diagram, fixture.bubble)
    const reopened = beginComprehensionDraft(cancelComprehensionDraft(opened), fixture.bubble)
    const matrix = (draft: typeof opened) => {
      const current = currentComprehensionDraft(draft)
      const rows: string[] = []
      for (const source of Object.keys(current.relation.diagram.wires)) {
        for (const target of Object.keys(current.relation.diagram.wires)) {
          const plan = planComprehensionConnection(draft, draftWire(source), draftWire(target))
          rows.push(`draft:${source}:${target}:${plan.ok ? plan.kind : plan.code}`)
        }
        for (const target of Object.keys(draft.host.wires)) {
          const plan = planComprehensionConnection(draft, draftWire(source), hostWire(target))
          rows.push(`host:${source}:${target}:${plan.ok ? plan.kind : plan.code}`)
          const reverse = planComprehensionConnection(draft, hostWire(target), draftWire(source))
          rows.push(`reverse-host:${target}:${source}:${reverse.ok ? reverse.kind : reverse.code}`)
        }
      }
      return rows
    }

    expect(matrix(reopened)).toEqual(matrix(opened))
  })

  it('canonicalizes binding order so different connection paths materialize identically', () => {
    const fixture = comprehensionFixture()
    const host = mkDiagram({
      root: fixture.diagram.root,
      regions: { ...fixture.diagram.regions },
      nodes: { ...fixture.diagram.nodes },
      wires: { ...fixture.diagram.wires, zHost: { scope: fixture.diagram.root, endpoints: [] } },
    })
    const start = beginComprehensionDraft(host, fixture.bubble)
    const left = applyComprehensionConnection(
      applyComprehensionConnection(start, draftWire('arg1'), hostWire('zHost')),
      draftWire('arg2'), hostWire(fixture.parameter),
    )
    const right = applyComprehensionConnection(
      applyComprehensionConnection(start, draftWire('arg2'), hostWire(fixture.parameter)),
      draftWire('arg1'), hostWire('zHost'),
    )
    expect(currentComprehensionDraft(left)).toEqual(currentComprehensionDraft(right))
    expect(materializeComprehensionSnapshot(currentComprehensionDraft(left)))
      .toEqual(materializeComprehensionSnapshot(currentComprehensionDraft(right)))
  })

  it('allows one already-bound draft identity to reference a different checked host wire', () => {
    const builder = new DiagramBuilder()
    const guard = builder.cut(builder.root)
    const bubble = builder.bubble(guard, 2)
    builder.atom(bubble, bubble)
    const firstHost = builder.wire(builder.root, [])
    const secondHost = builder.wire(builder.root, [])
    let draft = beginComprehensionDraft(builder.build(), bubble)
    draft = applyComprehensionConnection(draft, draftWire('arg1'), hostWire(firstHost))
    const plan = planComprehensionConnection(draft, draftWire('arg1'), hostWire(secondHost))
    expect(plan.ok).toBe(true)
    draft = applyComprehensionConnection(draft, draftWire('arg1'), hostWire(secondHost))
    expect(currentComprehensionDraft(draft).externalWires).toEqual([
      { draftWire: 'arg1', hostWire: firstHost },
      { draftWire: 'arg1', hostWire: secondHost },
    ])
    expect(() => commitComprehensionDraft(draft)).not.toThrow()
  })

  it('severs a graft without deleting its local wire and restores it through local history', () => {
    const { fixture, draft, wire } = draftWithConstant()
    let grafted = applyComprehensionConnection(draft, draftWire(wire), hostWire(fixture.parameter))
    grafted = ungraftComprehensionWire(grafted, wire)
    expect(currentComprehensionDraft(grafted).relation.diagram.wires[wire]).toBeDefined()
    expect(currentComprehensionDraft(grafted).externalWires).toEqual([])
    grafted = moveComprehensionHistory(grafted, -1)
    expect(currentComprehensionDraft(grafted).externalWires).toEqual([{ draftWire: wire, hostWire: fixture.parameter }])
  })

  it('removes a graft automatically when its final local use is deleted', () => {
    const { fixture, draft, wire, node } = draftWithConstant()
    const grafted = applyComprehensionConnection(draft, draftWire(wire), hostWire(fixture.parameter))
    const deleted = deleteComprehensionNode(grafted, node)
    const current = currentComprehensionDraft(deleted)
    expect(current.relation.diagram.wires[wire]).toBeUndefined()
    expect(current.externalWires).toEqual([])
    expect(current.relation.boundary).toEqual(['arg1', 'arg2'])
  })

  it('cancels by returning the exact host and commits through the real kernel rule', () => {
    const fixture = comprehensionFixture()
    const draft = beginComprehensionDraft(fixture.diagram, fixture.bubble)
    expect(cancelComprehensionDraft(draft)).toBe(fixture.diagram)
    const result = commitComprehensionDraft(draft)
    expect(result.regions[fixture.bubble]).toBeUndefined()
    expect(Object.values(result.nodes).some((node) => node.kind === 'atom' && node.binder === fixture.bubble)).toBe(false)
  })
})

describe('external-reference presentation', () => {
  it('marks canonical bindings and glows every host identified with one draft representative', () => {
    const bindings = [
      { draftWire: 'a', hostWire: 'x' },
      { draftWire: 'a', hostWire: 'y' },
      { draftWire: 'b', hostWire: 'z' },
    ]
    const fromDraft = deriveExternalReferencePresentation(bindings, new Set(['a']), new Set())
    expect([...fromDraft.markedDraft]).toEqual(['a', 'b'])
    expect([...fromDraft.markedHost]).toEqual(['x', 'y', 'z'])
    expect([...fromDraft.glowingDraft]).toEqual(['a'])
    expect([...fromDraft.glowingHost]).toEqual(['x', 'y'])

    const fromHost = deriveExternalReferencePresentation(bindings, new Set(), new Set(['y']))
    expect([...fromHost.glowingDraft]).toEqual(['a'])
    expect([...fromHost.glowingHost]).toEqual(['x', 'y'])
  })

  it('does not turn unrelated highlighted wires into external-reference marks', () => {
    const value = deriveExternalReferencePresentation(
      [{ draftWire: 'inside', hostWire: 'outside' }],
      new Set(['local']),
      new Set(['other']),
    )
    expect([...value.markedDraft]).toEqual(['inside'])
    expect([...value.markedHost]).toEqual(['outside'])
    expect(value.glowingDraft.size).toBe(0)
    expect(value.glowingHost.size).toBe(0)
  })
})
