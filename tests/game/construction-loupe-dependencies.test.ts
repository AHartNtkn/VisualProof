import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkDiagram, type Diagram, type DiagramNode, type RegionId, type Wire } from '../../src/kernel/diagram/diagram'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { planCopy } from '../../src/interaction/copy-planner'
import {
  applyCapturedComprehensionHostPatternImport,
  applyComprehensionConnection,
  beginComprehensionDraft,
  cancelComprehensionDraft,
  currentComprehensionDraft,
  importComprehensionHostBinderOccurrence,
  materializeComprehensionSnapshot,
  moveComprehensionHistory,
  planComprehensionHostPatternImport,
  replaceComprehensionDiagram,
  type ComprehensionSnapshot,
} from '../../src/game/interface/loupe/draft'
import type { ComprehensionDependencyState } from '../../src/interaction/comprehension-dependencies'
import { constructionInstantiationStep } from '../../src/game/interface/construction-loupe'
import { singleStepAction } from '../../src/kernel/proof/action'
import { EMPTY_PROOF_CONTEXT } from '../../src/kernel/proof/context'
import { applyGameAction, currentDiagram, type GameSession } from '../../src/game/session'
import { puzzleId } from '../../src/game/types'

function nestedHost(): {
  readonly diagram: Diagram
  readonly outer: RegionId
  readonly inner: RegionId
  readonly target: RegionId
  readonly inaccessible: RegionId
} {
  const builder = new DiagramBuilder()
  const outer = builder.bubble(builder.root, 1)
  const cut = builder.cut(outer)
  const inner = builder.bubble(cut, 2)
  const target = builder.bubble(inner, 0)
  const inaccessible = builder.bubble(builder.root, 3)
  return { diagram: builder.build(), outer, inner, target, inaccessible }
}

function dependency(snapshot: ComprehensionSnapshot): ComprehensionDependencyState {
  return snapshot.comprehension
}

function withoutNode(diagram: Diagram, nodeId: string): Diagram {
  const nodes: Record<string, DiagramNode> = Object.fromEntries(
    Object.entries(diagram.nodes).filter(([id]) => id !== nodeId),
  )
  const wires: Record<string, Wire> = Object.fromEntries(Object.entries(diagram.wires).flatMap(([id, wire]) => {
    const endpoints = wire.endpoints.filter((endpoint) => endpoint.node !== nodeId)
    return endpoints.length === 0 ? [] : [[id, { scope: wire.scope, endpoints }]]
  }))
  return mkDiagram({ root: diagram.root, regions: { ...diagram.regions }, nodes, wires })
}

describe('game construction dependency draft semantics', () => {
  it('begins with shared dependency state whose pattern is the current formal relation', () => {
    const host = nestedHost()
    const draft = beginComprehensionDraft(host.diagram, host.target)
    const snapshot = currentComprehensionDraft(draft)

    expect(snapshot.comprehension.dependencies).toEqual([])
    expect(snapshot.comprehension.pattern).toBe(snapshot.relation)
    expect(materializeComprehensionSnapshot(snapshot, host.diagram, host.target)).toEqual({
      relation: snapshot.relation,
      attachments: [],
      binders: [],
    })
  })

  it('imports menu occurrences in host order, reuses proxies, and materializes exact binders', () => {
    const host = nestedHost()
    let draft = beginComprehensionDraft(host.diagram, host.target)
    draft = importComprehensionHostBinderOccurrence(draft, host.inner, 2)
    draft = importComprehensionHostBinderOccurrence(draft, host.outer, 1)
    const once = currentComprehensionDraft(draft)
    const innerProxy = dependency(once).dependencies.find(([, target]) => target === host.inner)![0]

    draft = importComprehensionHostBinderOccurrence(draft, host.inner, 2)
    const snapshot = currentComprehensionDraft(draft)
    expect(dependency(snapshot).dependencies.map(([, target]) => target)).toEqual([host.outer, host.inner])
    expect(dependency(snapshot).dependencies.find(([, target]) => target === host.inner)![0]).toBe(innerProxy)
    expect(Object.values(snapshot.relation.diagram.nodes).filter(
      (node) => node.kind === 'atom' && node.binder === innerProxy,
    )).toHaveLength(2)
    expect(materializeComprehensionSnapshot(snapshot, host.diagram, host.target).binders)
      .toEqual(dependency(snapshot).dependencies)
  })

  it('maps a requested pre-import body to the post-import body', () => {
    const host = nestedHost()
    const outer = importComprehensionHostBinderOccurrence(
      beginComprehensionDraft(host.diagram, host.target), host.outer, 1,
    )
    const outerProxy = dependency(currentComprehensionDraft(outer)).dependencies[0]![0]

    const inner = importComprehensionHostBinderOccurrence(outer, host.inner, 2, outerProxy)
    const snapshot = currentComprehensionDraft(inner)
    const innerProxy = dependency(snapshot).dependencies[1]![0]
    const innerOccurrences = Object.values(snapshot.relation.diagram.nodes).filter(
      (node) => node.kind === 'atom' && node.binder === innerProxy,
    )

    expect(innerOccurrences).toEqual([{ kind: 'atom', region: innerProxy, binder: innerProxy }])
  })

  it('prunes a dead proxy on edit and refuses mutation of a live proxy', () => {
    const host = nestedHost()
    const imported = importComprehensionHostBinderOccurrence(
      beginComprehensionDraft(host.diagram, host.target), host.outer, 1,
    )
    const snapshot = currentComprehensionDraft(imported)
    const [node] = Object.keys(snapshot.relation.diagram.nodes)
    const proxy = dependency(snapshot).dependencies[0]![0]

    const pruned = replaceComprehensionDiagram(
      imported, withoutNode(snapshot.relation.diagram, node!),
    )
    expect(dependency(currentComprehensionDraft(pruned)).dependencies).toEqual([])
    expect(currentComprehensionDraft(pruned).relation.diagram.regions[proxy]).toBeUndefined()

    const proxyRegion = snapshot.relation.diagram.regions[proxy]
    if (proxyRegion?.kind !== 'bubble') throw new Error('expected live proxy')
    const cut = 'moved_under'
    const mutated = mkDiagram({
      root: snapshot.relation.diagram.root,
      regions: {
        ...snapshot.relation.diagram.regions,
        [cut]: { kind: 'cut', parent: snapshot.relation.diagram.root },
        [proxy]: { kind: 'bubble', parent: cut, arity: proxyRegion.arity },
      },
      nodes: { ...snapshot.relation.diagram.nodes },
      wires: { ...snapshot.relation.diagram.wires },
    })
    expect(() => replaceComprehensionDiagram(imported, mutated))
      .toThrow(/still-used proxy.*mutated/i)
    expect(imported.history).toHaveLength(2)
  })

  it('restores and discards relation, attachments, and binders atomically', () => {
    const builder = new DiagramBuilder()
    const binder = builder.bubble(builder.root, 0)
    const cut = builder.cut(binder)
    const target = builder.bubble(cut, 0)
    const host = builder.build()
    const initial = beginComprehensionDraft(host, target)
    const imported = importComprehensionHostBinderOccurrence(initial, binder, 0)
    const proxy = dependency(currentComprehensionDraft(imported)).dependencies[0]![0]

    const undone = moveComprehensionHistory(imported, -1)
    const undoSnapshot = currentComprehensionDraft(undone)
    expect(dependency(undoSnapshot).dependencies).toEqual([])
    expect(undoSnapshot.relation.diagram.regions[proxy]).toBeUndefined()
    expect(materializeComprehensionSnapshot(undoSnapshot, host, target).attachments).toEqual([])

    const redone = moveComprehensionHistory(undone, 1)
    expect(dependency(currentComprehensionDraft(redone)).dependencies).toEqual([[proxy, binder]])
    expect(cancelComprehensionDraft(redone)).toBe(host)
  })

  it('refuses inaccessible, stale-arity, and stale-draft menu inputs without history', () => {
    const host = nestedHost()
    const initial = beginComprehensionDraft(host.diagram, host.target)

    expect(() => importComprehensionHostBinderOccurrence(initial, host.inaccessible, 3))
      .toThrow(/properly enclose/i)
    expect(() => importComprehensionHostBinderOccurrence(initial, host.outer, 99))
      .toThrow(/arity.*changed/i)
    expect(initial.history).toHaveLength(1)
  })

  it('imports a selected nullary host atom through the dedicated route and matches menu state', () => {
    const builder = new DiagramBuilder()
    const binder = builder.bubble(builder.root, 0)
    const atom = builder.atom(binder, binder)
    const cut = builder.cut(binder)
    const target = builder.bubble(cut, 0)
    const host = builder.build()
    const selection = mkSelection(host, { region: binder, regions: [], nodes: [atom], wires: [] })
    const initial = beginComprehensionDraft(host, target)
    const snapshot = currentComprehensionDraft(initial)

    expect(planCopy(host, selection, {
      kind: 'workspace', draft: snapshot.relation.diagram,
      region: snapshot.relation.diagram.root, at: { x: 3, y: 4 },
    })).toMatchObject({ kind: 'refusal', code: 'external-binder' })

    const plan = planComprehensionHostPatternImport(
      initial, host, selection, snapshot.relation.diagram.root, { x: 3, y: 4 },
    )
    const selected = applyCapturedComprehensionHostPatternImport(initial, plan, host)
    const menu = importComprehensionHostBinderOccurrence(initial, binder, 0)

    expect(dependency(currentComprehensionDraft(selected)).dependencies)
      .toEqual(dependency(currentComprehensionDraft(menu)).dependencies)
    expect(plan.introduced).toHaveLength(1)
    expect(plan.at).toEqual({ x: 3, y: 4 })
  })

  it('keeps crossing selection wires loose and never converts them to host attachments', () => {
    const builder = new DiagramBuilder()
    const binder = builder.bubble(builder.root, 1)
    const atom = builder.atom(binder, binder)
    const outside = builder.ref(binder, 'outside', 1)
    builder.wire(binder, [
      { node: atom, port: { kind: 'arg', index: 0 } },
      { node: outside, port: { kind: 'arg', index: 0 } },
    ])
    const cut = builder.cut(binder)
    const target = builder.bubble(cut, 0)
    const host = builder.build()
    const selection = mkSelection(host, { region: binder, regions: [], nodes: [atom], wires: [] })
    const initial = beginComprehensionDraft(host, target)
    const plan = planComprehensionHostPatternImport(
      initial, host, selection, currentComprehensionDraft(initial).relation.diagram.root,
      { x: 8, y: 9 },
    )

    const imported = applyCapturedComprehensionHostPatternImport(initial, plan, host)
    const snapshot = currentComprehensionDraft(imported)
    const loose = Object.values(snapshot.relation.diagram.wires).find((wire) =>
      wire.endpoints.some((endpoint) => endpoint.node === plan.introduced[0]))

    expect(loose?.endpoints).toHaveLength(1)
    expect(snapshot.externalWires).toEqual([])
    expect(materializeComprehensionSnapshot(snapshot, host, target).attachments).toEqual([])
  })

  it('selected import remaps the pre-import body when it introduces an inner proxy', () => {
    const builder = new DiagramBuilder()
    const outer = builder.bubble(builder.root, 0)
    const cut = builder.cut(outer)
    const inner = builder.bubble(cut, 0)
    const atom = builder.atom(inner, inner)
    const target = builder.bubble(inner, 0)
    const host = builder.build()
    const withOuter = importComprehensionHostBinderOccurrence(
      beginComprehensionDraft(host, target), outer, 0,
    )
    const outerProxy = dependency(currentComprehensionDraft(withOuter)).dependencies[0]![0]
    const selection = mkSelection(host, { region: inner, regions: [], nodes: [atom], wires: [] })

    const plan = planComprehensionHostPatternImport(
      withOuter, host, selection, outerProxy, { x: 2, y: 3 },
    )
    const imported = applyCapturedComprehensionHostPatternImport(withOuter, plan, host)
    const innerProxy = dependency(currentComprehensionDraft(imported)).dependencies[1]![0]

    expect(currentComprehensionDraft(imported).relation.diagram.nodes[plan.introduced[0]!])
      .toEqual({ kind: 'atom', region: innerProxy, binder: innerProxy })
  })

  it('refuses inaccessible and stale selected imports without mutation', () => {
    const builder = new DiagramBuilder()
    const enclosing = builder.bubble(builder.root, 0)
    const cut = builder.cut(enclosing)
    const target = builder.bubble(cut, 0)
    const inaccessible = builder.bubble(builder.root, 0)
    const inaccessibleAtom = builder.atom(inaccessible, inaccessible)
    const accessibleAtom = builder.atom(enclosing, enclosing)
    const host = builder.build()
    const initial = beginComprehensionDraft(host, target)
    const inaccessibleSelection = mkSelection(host, {
      region: inaccessible, regions: [], nodes: [inaccessibleAtom], wires: [],
    })
    expect(() => planComprehensionHostPatternImport(
      initial, host, inaccessibleSelection, currentComprehensionDraft(initial).relation.diagram.root,
      { x: 0, y: 0 },
    )).toThrow(/properly enclose/i)

    const selection = mkSelection(host, {
      region: enclosing, regions: [], nodes: [accessibleAtom], wires: [],
    })
    const plan = planComprehensionHostPatternImport(
      initial, host, selection, currentComprehensionDraft(initial).relation.diagram.root,
      { x: 1, y: 2 },
    )
    const changed = importComprehensionHostBinderOccurrence(initial, enclosing, 0)
    const changedLength = changed.history.length
    expect(() => applyCapturedComprehensionHostPatternImport(changed, plan, host))
      .toThrow(/draft changed/i)
    expect(changed.history).toHaveLength(changedLength)
    expect(() => applyCapturedComprehensionHostPatternImport(
      initial, plan, mkDiagram({
        root: host.root, regions: { ...host.regions }, nodes: { ...host.nodes }, wires: { ...host.wires },
      }),
    )).toThrow(/source changed/i)
    expect(initial.history).toHaveLength(1)
  })

  it('keeps shared boundary state synchronized through wire-ledger mutations', () => {
    const builder = new DiagramBuilder()
    const binder = builder.bubble(builder.root, 0)
    const cut = builder.cut(binder)
    const target = builder.bubble(cut, 1)
    const atom = builder.atom(target, target)
    const parameter = builder.wire(binder, [{ node: atom, port: { kind: 'arg', index: 0 } }])
    const host = builder.build()
    let draft = beginComprehensionDraft(host, target)
    draft = importComprehensionHostBinderOccurrence(draft, binder, 0)
    draft = applyComprehensionConnection(
      draft,
      { kind: 'host', wire: parameter },
      { kind: 'draft', wire: 'arg1' },
    )
    const snapshot = currentComprehensionDraft(draft)
    const materialized = materializeComprehensionSnapshot(snapshot, host, target)

    expect(snapshot.comprehension.pattern.boundary).toEqual(materialized.relation.boundary)
    expect(materialized.attachments).toEqual([parameter])
    expect(materialized.binders).toEqual(snapshot.comprehension.dependencies)
  })

  it('emits exact binders and the normal game action path retains the intended host binding', () => {
    const builder = new DiagramBuilder()
    const binder = builder.bubble(builder.root, 0)
    const target = builder.bubble(binder, 0)
    builder.atom(target, target)
    const host = builder.build()
    const imported = importComprehensionHostBinderOccurrence(
      beginComprehensionDraft(host, target, 'backward'), binder, 0,
    )
    const pair = currentComprehensionDraft(imported).comprehension.dependencies[0]!
    const step = constructionInstantiationStep(imported)
    if (step.rule !== 'comprehensionInstantiate') {
      throw new Error('construction must emit comprehension instantiation')
    }
    const session: GameSession = {
      puzzle: puzzleId('binder-import'),
      timeline: { states: [host], actions: [], cursor: 0 },
    }

    expect(step.binders).toEqual([pair])
    const applied = applyGameAction(
      session,
      singleStepAction(step.rule, step),
      { context: EMPTY_PROOF_CONTEXT, artifact: () => undefined },
    )
    const result = currentDiagram(applied.session)
    expect(Object.values(result.nodes).filter(
      (node) => node.kind === 'atom' && node.binder === binder,
    )).toHaveLength(1)
  })
})
