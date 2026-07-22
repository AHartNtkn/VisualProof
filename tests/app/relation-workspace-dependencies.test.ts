import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkDiagram, type Diagram, type WireId } from '../../src/kernel/diagram/diagram'
import { relSig, TERM } from '../../src/kernel/diagram/sig'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { planCopy } from '../../src/app/copy-planner'
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
  importRelationHostOccurrence,
  materializeRelationDraft,
  moveRelationHistory,
  planRelationHostPatternImport,
  replaceRelationDiagram,
  type RelationWorkspaceSnapshot,
} from '../../src/app/relation-workspace-draft'

// The old proxy-region ComprehensionDependencyState machinery is gone: in the
// wire model an outer-bound dependency is simply an optional draft PORT whose
// `hostWire` names the enclosing relational line, and the body's occurrences are
// bound atoms riding that draft PARAM wire. Wire identity IS head-wire identity, so
// the intricate proxy bookkeeping (prefix repair, nested-proxy dedup/remapping,
// proxy pruning, proxy-mutation refusal) has NO successor; the capability those
// tests protected — referencing outer relation wires and materializing them as macro
// parameters — is re-expressed below directly on the port model. Four former
// tests were pure proxy-state-machine mechanics with no wire-model counterpart:
// "remaps a requested pre-import effective body", "prunes a proxy on deleting the
// last occurrence", "refuses mutation/removal of a live proxy", and "selected
// import remaps the pre-import effective body" — deleted, not ported.

/** Outer relwire /1, an inner relwire /2, and the /0 target all enclose the target scope. */
function nestedHost(): {
  readonly diagram: Diagram
  readonly outer: WireId
  readonly inner: WireId
  readonly target: WireId
} {
  const builder = new DiagramBuilder()
  const outer = builder.relWire(builder.root, relSig([TERM]))
  const cut = builder.cut(builder.root)
  const inner = builder.relWire(cut, relSig([TERM, TERM]))
  const target = builder.relWire(cut, relSig([]))
  return { diagram: builder.build(), outer, inner, target }
}

/** Number of atom heads riding `wireId`. */
function headOccurrences(snapshot: RelationWorkspaceSnapshot, wireId: WireId): number {
  return (snapshot.diagram.wires[wireId]?.endpoints ?? []).filter(
    (ep) => ep.port.kind === 'head' && snapshot.diagram.nodes[ep.node]?.kind === 'atom',
  ).length
}

describe('relation workspace outer-bound dependencies', () => {
  it('imports one outer host relation wire as a param port with a bound occurrence riding its draft wire', () => {
    const host = nestedHost()
    const initial = beginSubstitutionDraft(host.diagram, host.target)

    const imported = importRelationHostOccurrence(
      initial, host.outer, currentRelationDraft(initial).diagram.root,
    )
    const snapshot = currentRelationDraft(imported)

    expect(imported.history).toHaveLength(initial.history.length + 1)
    expect(snapshot.ports).toHaveLength(1)
    const port = snapshot.ports[0]!
    expect(port).toMatchObject({ kind: 'optional', hostWire: host.outer })
    expect(headOccurrences(snapshot, port.wire)).toBe(1)
    expect(materializeRelationDraft(imported)).toMatchObject({ attachments: [host.outer], params: [host.outer] })
  })

  it('reuses one param designation for a repeated host relation wire import, accumulating occurrences', () => {
    const host = nestedHost()
    let draft = beginSubstitutionDraft(host.diagram, host.target)
    draft = importRelationHostOccurrence(draft, host.inner)
    draft = importRelationHostOccurrence(draft, host.outer)
    const innerPort = currentRelationDraft(draft).ports.find((port) => port.hostWire === host.inner)!

    draft = importRelationHostOccurrence(draft, host.inner)
    const twice = currentRelationDraft(draft)

    expect(twice.ports.filter((port) => port.hostWire === host.inner)).toHaveLength(1)
    expect(twice.ports.find((port) => port.hostWire === host.inner)!.wire).toBe(innerPort.wire)
    expect(headOccurrences(twice, innerPort.wire)).toBe(2)
    expect(materializeRelationDraft(draft).params).toEqual([host.inner, host.outer])
  })

  it('restores param designations through undo/redo and cancellation preserves the host', () => {
    const host = nestedHost()
    const initial = beginSubstitutionDraft(host.diagram, host.target)
    const imported = importRelationHostOccurrence(initial, host.outer)

    const undone = moveRelationHistory(imported, -1)
    expect(currentRelationDraft(undone).ports).toEqual([])

    const redone = moveRelationHistory(undone, 1)
    expect(currentRelationDraft(redone).ports).toEqual([
      expect.objectContaining({ kind: 'optional', hostWire: host.outer }),
    ])
    expect(cancelRelationDraft(redone)).toBe(host.diagram)
  })

  it('does not give abstraction snapshots dependency ports and refuses host relation wire import', () => {
    const host = nestedHost()
    const draft = beginAbstractionDraft(host.diagram)

    expect(currentRelationDraft(draft)).not.toHaveProperty('comprehension')
    expect(() => importRelationHostOccurrence(draft, host.outer)).toThrow(/substitution/i)
    expect(draft.history).toHaveLength(1)
  })

  it('dedicated host-pattern import designates the open outer-bound atom as a param, matching menu designation', () => {
    const builder = new DiagramBuilder()
    const guard = builder.cut(builder.root)
    const atom = builder.atom(guard, relSig([]))
    const hostRelation = builder.wire(builder.root, [{ node: atom, port: { kind: 'head' } }], relSig([]))
    const target = builder.relWire(guard, relSig([]))
    const host = builder.build()
    const selection = mkSelection(host, { region: guard, regions: [], nodes: [atom], wires: [] })
    const initial = beginSubstitutionDraft(host, target)
    const current = currentRelationDraft(initial)

    // Generic copy no longer refuses an outer-bound atom — a crossing relational
    // wire is a legitimate higher-order argument — but it does NOT designate the
    // enclosing relation wire as an outer-bound parameter. The dedicated import does.
    const copied = planCopy(host, selection, {
      kind: 'workspace', draft: current.diagram, region: current.diagram.root, at: { x: 3, y: 4 },
    })
    expect(copied.kind).toBe('workspace')

    const planned = planRelationHostPatternImport(
      initial, host, selection, current.diagram.root, { x: 3, y: 4 },
    )
    const imported = applyCapturedRelationHostPatternImport(initial, planned, host)
    const menuImported = importRelationHostOccurrence(initial, hostRelation)

    const designation = (snapshot: RelationWorkspaceSnapshot) =>
      snapshot.ports.map((port) => ({ kind: port.kind, hostWire: port.hostWire }))
    expect(designation(currentRelationDraft(imported))).toEqual(designation(currentRelationDraft(menuImported)))
    expect(planned.introduced).toHaveLength(1)
    expect(planned.at).toEqual({ x: 3, y: 4 })
    const importedPort = currentRelationDraft(imported).ports[0]!
    expect(importedPort).toMatchObject({ kind: 'optional', hostWire: hostRelation })
    expect(headOccurrences(currentRelationDraft(imported), importedPort.wire)).toBe(1)
  })

  it('turns a relational crossing into a deduped param port while keeping a term crossing loose', () => {
    const builder = new DiagramBuilder()
    const guard = builder.cut(builder.root)
    const atom = builder.atom(guard, relSig([TERM]))
    const hostRelation = builder.wire(builder.root, [{ node: atom, port: { kind: 'head' } }], relSig([TERM]))
    const outside = builder.ref(guard, 'outside', relSig([TERM]))
    const crossing = builder.wire(guard, [
      { node: atom, port: { kind: 'arg', index: 0 } },
      { node: outside, port: { kind: 'arg', index: 0 } },
    ], TERM)
    const target = builder.relWire(guard, relSig([]))
    const host = builder.build()
    const selection = mkSelection(host, { region: guard, regions: [], nodes: [atom], wires: [] })
    const initial = beginSubstitutionDraft(host, target)
    const planned = planRelationHostPatternImport(
      initial, host, selection, currentRelationDraft(initial).diagram.root, { x: 8, y: 9 },
    )

    const imported = applyCapturedRelationHostPatternImport(initial, planned, host)
    const snapshot = currentRelationDraft(imported)
    const introduced = planned.introduced[0]!
    const looseTermWire = Object.values(snapshot.diagram.wires).find((wire) =>
      wire.sig.kind === 'term' && wire.endpoints.length === 1 && wire.endpoints.some((ep) => ep.node === introduced))

    expect(crossing).toBeTruthy()
    // The head crossing became a param port; the term arg crossing stayed a loose
    // draft wire carrying only the copied atom's arg — never a host attachment.
    expect(snapshot.ports).toEqual([expect.objectContaining({ kind: 'optional', hostWire: hostRelation })])
    expect(looseTermWire).toBeDefined()
    expect(materializeRelationDraft(imported).params).toEqual([hostRelation])
  })

  it('refuses inaccessible and stale host-pattern imports without mutating history', () => {
    const builder = new DiagramBuilder()
    const enclosing = builder.cut(builder.root)
    const target = builder.relWire(enclosing, relSig([]))
    const sibling = builder.cut(builder.root)
    const atom = builder.atom(sibling, relSig([]))
    builder.wire(sibling, [{ node: atom, port: { kind: 'head' } }], relSig([]))
    const host = builder.build()
    const inaccessibleSelection = mkSelection(host, { region: sibling, regions: [], nodes: [atom], wires: [] })
    const initial = beginSubstitutionDraft(host, target)

    expect(() => planRelationHostPatternImport(
      initial, host, inaccessibleSelection, currentRelationDraft(initial).diagram.root, { x: 0, y: 0 },
    )).toThrow(/properly enclose/i)
    expect(initial.history).toHaveLength(1)

    const accessibleBuilder = new DiagramBuilder()
    const accessibleEnclosing = accessibleBuilder.cut(accessibleBuilder.root)
    const accessibleTarget = accessibleBuilder.relWire(accessibleEnclosing, relSig([]))
    const accessibleAtom = accessibleBuilder.atom(accessibleEnclosing, relSig([]))
    const accessibleHostRelation = accessibleBuilder.wire(
      accessibleBuilder.root, [{ node: accessibleAtom, port: { kind: 'head' } }], relSig([]),
    )
    const accessibleHost = accessibleBuilder.build()
    const accessible = beginSubstitutionDraft(accessibleHost, accessibleTarget)
    const selection = mkSelection(accessibleHost, {
      region: accessibleEnclosing, regions: [], nodes: [accessibleAtom], wires: [],
    })
    const plan = planRelationHostPatternImport(
      accessible, accessibleHost, selection, currentRelationDraft(accessible).diagram.root, { x: 1, y: 2 },
    )
    const changed = importRelationHostOccurrence(accessible, accessibleHostRelation)
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
    const enclosing = builder.cut(builder.root)
    const target = builder.relWire(enclosing, relSig([]))
    const sibling = builder.cut(builder.root)
    const atom = builder.atom(sibling, relSig([]))
    builder.wire(sibling, [{ node: atom, port: { kind: 'head' } }], relSig([]))
    const host = builder.build()
    const draft = beginSubstitutionDraft(host, target)
    const selection = mkSelection(host, { region: sibling, regions: [], nodes: [atom], wires: [] })

    expect(planRelationHostPatternDrop(
      draft, host, selection, currentRelationDraft(draft).diagram.root, { x: 4, y: 5 },
    )).toEqual({
      plan: null,
      refusal: expect.stringMatching(/properly enclose/i),
    })
  })

  it('commits host-pattern drops against authoritative live source state, independent of render rebuilds', () => {
    const builder = new DiagramBuilder()
    const enclosing = builder.cut(builder.root)
    const target = builder.relWire(enclosing, relSig([]))
    const atom = builder.atom(enclosing, relSig([]))
    builder.wire(builder.root, [{ node: atom, port: { kind: 'head' } }], relSig([]))
    const host = builder.build()
    const draft = beginSubstitutionDraft(host, target)
    const selection = mkSelection(host, { region: enclosing, regions: [], nodes: [atom], wires: [] })
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

  it('keeps source-tagged draft and host relation wire menu candidates distinct under equal wire ids', () => {
    const host = mkDiagram({
      root: 'r0',
      regions: { r0: { kind: 'sheet' }, guard: { kind: 'cut', parent: 'r0' } },
      wires: {
        hb: { scope: 'r0', sig: relSig([]), endpoints: [] },
        target: { scope: 'guard', sig: relSig([]), endpoints: [] },
      },
    })
    let draft = beginSubstitutionDraft(host, 'target')
    const current = currentRelationDraft(draft)
    draft = replaceRelationDiagram(draft, mkDiagram({
      root: current.diagram.root,
      regions: { ...current.diagram.regions },
      wires: { ...current.diagram.wires, hb: { scope: current.diagram.root, sig: relSig([]), endpoints: [] } },
    }))

    expect(relationWorkspaceBoundPredicateOptions(draft, current.diagram.root).filter(
      (option) => option.wire === 'hb',
    )).toEqual([
      { source: 'draft', wire: 'hb', arity: 0, position: 1, total: 1 },
      { source: 'host', wire: 'hb', arity: 0, position: 1, total: 1 },
    ])
  })

  it('labels canonical inner-to-outer host menu ancestors by their true nesting position', () => {
    const host = nestedHost()
    const draft = beginSubstitutionDraft(host.diagram, host.target)

    expect(relationWorkspaceBoundPredicateOptions(
      draft, currentRelationDraft(draft).diagram.root,
    ).filter((option) => option.source === 'host')).toEqual([
      { source: 'host', wire: host.inner, arity: 2, position: 1, total: 2 },
      { source: 'host', wire: host.outer, arity: 1, position: 2, total: 2 },
    ])
  })

  it('routes only open substitution host selections to dependency import', () => {
    const builder = new DiagramBuilder()
    const outerGuard = builder.cut(builder.root)
    const openAtom = builder.atom(outerGuard, relSig([]))
    builder.wire(builder.root, [{ node: openAtom, port: { kind: 'head' } }], relSig([]))
    const closedGuard = builder.cut(builder.root)
    const closedAtom = builder.atom(closedGuard, relSig([]))
    builder.wire(closedGuard, [{ node: closedAtom, port: { kind: 'head' } }], relSig([]))
    const target = builder.relWire(builder.root, relSig([]))
    const host = builder.build()
    const open = mkSelection(host, { region: outerGuard, regions: [], nodes: [openAtom], wires: [] })
    const closed = mkSelection(host, { region: builder.root, regions: [closedGuard], nodes: [], wires: [] })

    expect(relationHostSelectionRoute(beginSubstitutionDraft(host, target), host, open)).toBe('import')
    expect(relationHostSelectionRoute(beginSubstitutionDraft(host, target), host, closed)).toBe('copy')
    expect(relationHostSelectionRoute(beginAbstractionDraft(host), host, open)).toBe('refused')
  })
})
