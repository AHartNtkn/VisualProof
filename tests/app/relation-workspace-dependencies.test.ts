import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkDiagram, type Diagram, type DiagramNode, type RegionId, type Wire } from '../../src/kernel/diagram/diagram'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { planCopy } from '../../src/interaction/copy-planner'
import {
  applyRelationHostPatternDrop,
  planRelationHostPatternDrop,
  relationHostSelectionRoute,
  relationWorkspaceBoundPredicateOptions,
} from '../../src/app/relation-workspace'
import {
  applyCapturedRelationHostPatternImport,
  beginAbstractionDraft,
  beginSubstitutionDraft,
  cancelRelationDraft,
  currentRelationDraft,
  importRelationHostBinderOccurrence,
  materializeRelationDraft,
  moveRelationHistory,
  planRelationHostPatternImport,
  replaceRelationDiagram,
  type RelationWorkspaceSnapshot,
} from '../../src/app/relation-workspace-draft'
import type { ComprehensionDependencyState } from '../../src/interaction/comprehension-dependencies'

function nestedHost(): {
  readonly diagram: Diagram
  readonly outer: RegionId
  readonly inner: RegionId
  readonly target: RegionId
} {
  const builder = new DiagramBuilder()
  const outer = builder.bubble(builder.root, 1)
  const cut = builder.cut(outer)
  const inner = builder.bubble(cut, 2)
  const target = builder.bubble(inner, 0)
  return { diagram: builder.build(), outer, inner, target }
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

function comprehension(snapshot: RelationWorkspaceSnapshot): ComprehensionDependencyState {
  if (snapshot.comprehension === undefined) throw new Error('expected substitution dependency state')
  return snapshot.comprehension
}

describe('relation workspace comprehension dependencies', () => {
  it('imports one host binder at a requested root as the exact materialized pair', () => {
    const host = nestedHost()
    const initial = beginSubstitutionDraft(host.diagram, host.target)

    const imported = importRelationHostBinderOccurrence(
      initial, host.outer, currentRelationDraft(initial).diagram.root,
    )
    const snapshot = currentRelationDraft(imported)
    const state = comprehension(snapshot)
    const [pair] = state.dependencies
    const [proxy] = pair!
    const [nodeId] = Object.keys(snapshot.diagram.nodes)

    expect(imported.history).toHaveLength(initial.history.length + 1)
    expect(pair).toEqual([proxy, host.outer])
    expect(snapshot.diagram.nodes[nodeId!]).toEqual({ kind: 'atom', region: proxy, binder: proxy })
    expect(materializeRelationDraft(imported)).toEqual({
      relation: state.pattern,
      attachments: [],
      binders: [[proxy, host.outer]],
    })
  })

  it('orders outer and inner imports canonically and reuses a duplicate proxy', () => {
    const host = nestedHost()
    let draft = beginSubstitutionDraft(host.diagram, host.target)
    draft = importRelationHostBinderOccurrence(draft, host.inner)
    draft = importRelationHostBinderOccurrence(draft, host.outer)
    const once = currentRelationDraft(draft)
    const innerProxy = comprehension(once).dependencies.find(([, target]) => target === host.inner)![0]

    draft = importRelationHostBinderOccurrence(draft, host.inner)
    const twice = currentRelationDraft(draft)

    expect(comprehension(twice).dependencies.map(([, target]) => target)).toEqual([host.outer, host.inner])
    expect(comprehension(twice).dependencies.find(([, target]) => target === host.inner)![0]).toBe(innerProxy)
    expect(Object.values(twice.diagram.nodes).filter(
      (node) => node.kind === 'atom' && node.binder === innerProxy,
    )).toHaveLength(2)
  })

  it('remaps a requested pre-import effective body to the new inner dependency body', () => {
    const host = nestedHost()
    const outer = importRelationHostBinderOccurrence(
      beginSubstitutionDraft(host.diagram, host.target), host.outer,
    )
    const outerProxy = comprehension(currentRelationDraft(outer)).dependencies[0]![0]

    const inner = importRelationHostBinderOccurrence(outer, host.inner, outerProxy)
    const state = comprehension(currentRelationDraft(inner))
    const innerProxy = state.dependencies[1]![0]
    const innerOccurrences = Object.values(currentRelationDraft(inner).diagram.nodes).filter(
      (node) => node.kind === 'atom' && node.binder === innerProxy,
    )

    expect(innerOccurrences).toEqual([{ kind: 'atom', region: innerProxy, binder: innerProxy }])
  })

  it('reconciles every diagram replacement so deleting the last occurrence prunes its proxy', () => {
    const host = nestedHost()
    const imported = importRelationHostBinderOccurrence(
      beginSubstitutionDraft(host.diagram, host.target), host.outer,
    )
    const snapshot = currentRelationDraft(imported)
    const node = Object.keys(snapshot.diagram.nodes)[0]!
    const proxy = comprehension(snapshot).dependencies[0]![0]

    const pruned = replaceRelationDiagram(imported, withoutNode(snapshot.diagram, node))

    expect(comprehension(currentRelationDraft(pruned)).dependencies).toEqual([])
    expect(currentRelationDraft(pruned).diagram.regions[proxy]).toBeUndefined()
  })

  it('refuses mutation or removal of a live proxy without appending history', () => {
    const host = nestedHost()
    const imported = importRelationHostBinderOccurrence(
      beginSubstitutionDraft(host.diagram, host.target), host.outer,
    )
    const snapshot = currentRelationDraft(imported)
    const proxy = comprehension(snapshot).dependencies[0]![0]
    const proxyRegion = snapshot.diagram.regions[proxy]
    if (proxyRegion?.kind !== 'bubble') throw new Error('expected live proxy bubble')
    const cut = 'moved_under'
    const mutated = mkDiagram({
      root: snapshot.diagram.root,
      regions: {
        ...snapshot.diagram.regions,
        [cut]: { kind: 'cut', parent: snapshot.diagram.root },
        [proxy]: { kind: 'bubble', parent: cut, arity: proxyRegion.arity },
      },
      nodes: { ...snapshot.diagram.nodes },
      wires: { ...snapshot.diagram.wires },
    })

    expect(() => replaceRelationDiagram(imported, mutated)).toThrow(/still-used proxy.*mutated/i)
    expect(imported.history).toHaveLength(2)
    expect(currentRelationDraft(imported)).toBe(snapshot)
  })

  it('restores dependency state atomically through undo/redo and cancellation preserves the host', () => {
    const host = nestedHost()
    const initial = beginSubstitutionDraft(host.diagram, host.target)
    const imported = importRelationHostBinderOccurrence(initial, host.outer)
    const proxy = comprehension(currentRelationDraft(imported)).dependencies[0]![0]

    const undone = moveRelationHistory(imported, -1)
    expect(comprehension(currentRelationDraft(undone)).dependencies).toEqual([])
    expect(currentRelationDraft(undone).diagram.regions[proxy]).toBeUndefined()

    const redone = moveRelationHistory(undone, 1)
    expect(comprehension(currentRelationDraft(redone)).dependencies).toEqual([[proxy, host.outer]])
    expect(cancelRelationDraft(redone)).toBe(host.diagram)
  })

  it('does not give abstraction snapshots dependency state and refuses host binder import', () => {
    const host = nestedHost()
    const draft = beginAbstractionDraft(host.diagram)

    expect(currentRelationDraft(draft)).not.toHaveProperty('comprehension')
    expect(() => importRelationHostBinderOccurrence(draft, host.outer)).toThrow(/substitution/i)
    expect(draft.history).toHaveLength(1)
  })

  it('dedicated host-pattern import accepts the open nullary atom refused by generic copy and matches menu dependency state', () => {
    const builder = new DiagramBuilder()
    const binder = builder.bubble(builder.root, 0)
    const atom = builder.atom(binder, binder)
    const target = builder.bubble(binder, 0)
    const host = builder.build()
    const selection = mkSelection(host, { region: binder, regions: [], nodes: [atom], wires: [] })
    const initial = beginSubstitutionDraft(host, target)
    const current = currentRelationDraft(initial)

    expect(planCopy(host, selection, {
      kind: 'workspace', draft: current.diagram, region: current.diagram.root, at: { x: 3, y: 4 },
    })).toMatchObject({ kind: 'refusal', code: 'external-binder' })

    const planned = planRelationHostPatternImport(
      initial, host, selection, current.diagram.root, { x: 3, y: 4 },
    )
    const imported = applyCapturedRelationHostPatternImport(initial, planned, host)
    const menuImported = importRelationHostBinderOccurrence(initial, binder)

    expect(comprehension(currentRelationDraft(imported)).dependencies)
      .toEqual(comprehension(currentRelationDraft(menuImported)).dependencies)
    expect(planned.introduced).toHaveLength(1)
    expect(planned.at).toEqual({ x: 3, y: 4 })
    expect(Object.values(currentRelationDraft(imported).diagram.nodes)).toEqual([
      expect.objectContaining({ kind: 'atom', binder: planned.binders[0]![0] }),
    ])
  })

  it('keeps crossing host-pattern wires loose instead of creating host attachment ports', () => {
    const builder = new DiagramBuilder()
    const binder = builder.bubble(builder.root, 1)
    const atom = builder.atom(binder, binder)
    const outside = builder.ref(binder, 'outside', 1)
    const crossing = builder.wire(binder, [
      { node: atom, port: { kind: 'arg', index: 0 } },
      { node: outside, port: { kind: 'arg', index: 0 } },
    ])
    const target = builder.bubble(binder, 0)
    const host = builder.build()
    const selection = mkSelection(host, { region: binder, regions: [], nodes: [atom], wires: [] })
    const initial = beginSubstitutionDraft(host, target)
    const planned = planRelationHostPatternImport(
      initial, host, selection, currentRelationDraft(initial).diagram.root, { x: 8, y: 9 },
    )

    const imported = applyCapturedRelationHostPatternImport(initial, planned, host)
    const snapshot = currentRelationDraft(imported)
    const loose = Object.entries(snapshot.diagram.wires).find(([, wire]) =>
      wire.endpoints.some((endpoint) => endpoint.node === planned.introduced[0]))

    expect(crossing).toBeTruthy()
    expect(loose?.[1].endpoints).toHaveLength(1)
    expect(snapshot.ports).toEqual([])
    expect(materializeRelationDraft(imported).attachments).toEqual([])
  })

  it('selected import also remaps the pre-import effective body when it introduces an inner proxy', () => {
    const builder = new DiagramBuilder()
    const outer = builder.bubble(builder.root, 0)
    const cut = builder.cut(outer)
    const inner = builder.bubble(cut, 0)
    const atom = builder.atom(inner, inner)
    const target = builder.bubble(inner, 0)
    const host = builder.build()
    const withOuter = importRelationHostBinderOccurrence(beginSubstitutionDraft(host, target), outer)
    const outerProxy = comprehension(currentRelationDraft(withOuter)).dependencies[0]![0]
    const selection = mkSelection(host, { region: inner, regions: [], nodes: [atom], wires: [] })

    const planned = planRelationHostPatternImport(
      withOuter, host, selection, outerProxy, { x: 2, y: 3 },
    )
    const imported = applyCapturedRelationHostPatternImport(withOuter, planned, host)
    const innerProxy = comprehension(currentRelationDraft(imported)).dependencies[1]![0]

    expect(currentRelationDraft(imported).diagram.nodes[planned.introduced[0]!]).toEqual({
      kind: 'atom', region: innerProxy, binder: innerProxy,
    })
  })

  it('refuses inaccessible and stale host-pattern imports without mutating history', () => {
    const builder = new DiagramBuilder()
    const enclosing = builder.bubble(builder.root, 0)
    const target = builder.bubble(enclosing, 0)
    const inaccessible = builder.bubble(builder.root, 0)
    const atom = builder.atom(inaccessible, inaccessible)
    const host = builder.build()
    const inaccessibleSelection = mkSelection(host, {
      region: inaccessible, regions: [], nodes: [atom], wires: [],
    })
    const initial = beginSubstitutionDraft(host, target)

    expect(() => planRelationHostPatternImport(
      initial, host, inaccessibleSelection, currentRelationDraft(initial).diagram.root, { x: 0, y: 0 },
    )).toThrow(/properly enclose/i)
    expect(initial.history).toHaveLength(1)

    const accessibleAtom = builder.atom(enclosing, enclosing)
    const accessibleHost = builder.build()
    const accessible = beginSubstitutionDraft(accessibleHost, target)
    const selection = mkSelection(accessibleHost, {
      region: enclosing, regions: [], nodes: [accessibleAtom], wires: [],
    })
    const plan = planRelationHostPatternImport(
      accessible, accessibleHost, selection, currentRelationDraft(accessible).diagram.root, { x: 1, y: 2 },
    )
    const changed = importRelationHostBinderOccurrence(accessible, enclosing)
    const changedLength = changed.history.length

    expect(() => applyCapturedRelationHostPatternImport(changed, plan, accessibleHost)).toThrow(/draft changed/i)
    expect(changed.history).toHaveLength(changedLength)
    expect(() => applyCapturedRelationHostPatternImport(
      accessible, plan, mkDiagram({
        root: accessibleHost.root,
        regions: { ...accessibleHost.regions },
        nodes: { ...accessibleHost.nodes },
        wires: { ...accessibleHost.wires },
      }),
    )).toThrow(/source changed/i)
    expect(accessible.history).toHaveLength(1)
  })

  it('retains an inaccessible host-pattern planning refusal for the drag release seam', () => {
    const builder = new DiagramBuilder()
    const enclosing = builder.bubble(builder.root, 0)
    const target = builder.bubble(enclosing, 0)
    const inaccessible = builder.bubble(builder.root, 0)
    const atom = builder.atom(inaccessible, inaccessible)
    const host = builder.build()
    const draft = beginSubstitutionDraft(host, target)
    const selection = mkSelection(host, {
      region: inaccessible, regions: [], nodes: [atom], wires: [],
    })

    expect(planRelationHostPatternDrop(
      draft, host, selection, currentRelationDraft(draft).diagram.root, { x: 4, y: 5 },
    )).toEqual({
      plan: null,
      refusal: expect.stringMatching(/properly enclose/i),
    })
  })

  it('commits host-pattern drops against authoritative live source state, independent of render rebuilds', () => {
    const builder = new DiagramBuilder()
    const enclosing = builder.bubble(builder.root, 0)
    const atom = builder.atom(enclosing, enclosing)
    const target = builder.bubble(enclosing, 0)
    const host = builder.build()
    const draft = beginSubstitutionDraft(host, target)
    const selection = mkSelection(host, {
      region: enclosing, regions: [], nodes: [atom], wires: [],
    })
    const plan = planRelationHostPatternImport(
      draft, host, selection, currentRelationDraft(draft).diagram.root, { x: 1, y: 2 },
    )
    const rebuiltRenderDiagram = mkDiagram({
      root: host.root,
      regions: { ...host.regions },
      nodes: { ...host.nodes },
      wires: { ...host.wires },
    })

    expect(rebuiltRenderDiagram).not.toBe(host)
    expect(() => applyCapturedRelationHostPatternImport(
      draft, plan, rebuiltRenderDiagram,
    )).toThrow(/source changed/i)
    expect(applyRelationHostPatternDrop(
      draft, plan, { liveSourceDiagram: () => host },
    ).history).toHaveLength(2)

    const changedLiveSource = new DiagramBuilder().build()
    expect(() => applyRelationHostPatternDrop(
      draft, plan, { liveSourceDiagram: () => changedLiveSource },
    )).toThrow(/source changed/i)
  })

  it('keeps source-tagged draft and host binder menu candidates distinct under equal region ids', () => {
    const hostBuilder = new DiagramBuilder()
    const hostBinder = hostBuilder.bubble(hostBuilder.root, 0)
    const target = hostBuilder.bubble(hostBinder, 0)
    const host = hostBuilder.build()
    let draft = beginSubstitutionDraft(host, target)
    const current = currentRelationDraft(draft)
    draft = replaceRelationDiagram(draft, mkDiagram({
      root: current.diagram.root,
      regions: {
        ...current.diagram.regions,
        [hostBinder]: { kind: 'bubble', parent: current.diagram.root, arity: 0 },
      },
      nodes: { ...current.diagram.nodes },
      wires: { ...current.diagram.wires },
    }))

    expect(relationWorkspaceBoundPredicateOptions(draft, hostBinder).filter(
      (option) => option.binder === hostBinder,
    )).toEqual([
      { source: 'draft', binder: hostBinder, arity: 0, position: 1, total: 1 },
      { source: 'host', binder: hostBinder, arity: 0, position: 1, total: 1 },
    ])
  })

  it('labels canonical outer-to-inner host menu ancestors by their true nesting position', () => {
    const host = nestedHost()
    const draft = beginSubstitutionDraft(host.diagram, host.target)

    expect(relationWorkspaceBoundPredicateOptions(
      draft, currentRelationDraft(draft).diagram.root,
    ).filter((option) => option.source === 'host')).toEqual([
      { source: 'host', binder: host.outer, arity: 1, position: 2, total: 2 },
      { source: 'host', binder: host.inner, arity: 2, position: 1, total: 2 },
    ])
  })

  it('routes only open substitution host selections to dependency import', () => {
    const builder = new DiagramBuilder()
    const binder = builder.bubble(builder.root, 0)
    const atom = builder.atom(binder, binder)
    const target = builder.bubble(binder, 0)
    const host = builder.build()
    const open = mkSelection(host, { region: binder, regions: [], nodes: [atom], wires: [] })
    const closed = mkSelection(host, { region: builder.root, regions: [binder], nodes: [], wires: [] })

    expect(relationHostSelectionRoute(beginSubstitutionDraft(host, target), host, open)).toBe('import')
    expect(relationHostSelectionRoute(beginSubstitutionDraft(host, target), host, closed)).toBe('copy')
    expect(relationHostSelectionRoute(beginAbstractionDraft(host), host, open)).toBe('refused')
  })
})
