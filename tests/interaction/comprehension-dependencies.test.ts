import { describe, expect, it } from 'vitest'
import { mkDiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkDiagram, type Diagram, type DiagramNode, type Wire } from '../../src/kernel/diagram/diagram'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { parseTerm } from '../../src/kernel/term/parse'
import {
  addComprehensionBoundOccurrence,
  assertComprehensionProxyEditable,
  createComprehensionDependencyState,
  enclosingComprehensionBinders,
  importComprehensionDependency,
  materializeComprehensionDependencies,
  mergeSelectedComprehensionDependencies,
  reconcileComprehensionDependencies,
  validateComprehensionDependencies,
} from '../../src/interaction/comprehension-dependencies'

const p = (source: string) => parseTerm(source)

function emptyPattern() {
  const builder = new DiagramBuilder()
  return mkDiagramWithBoundary(builder.build(), [])
}

function nestedHost(): {
  readonly diagram: Diagram
  readonly outer: string
  readonly inner: string
  readonly target: string
  readonly inaccessible: string
} {
  const builder = new DiagramBuilder()
  const outer = builder.bubble(builder.root, 1)
  const cut = builder.cut(outer)
  const inner = builder.bubble(cut, 2)
  const target = builder.bubble(inner, 0)
  const inaccessible = builder.bubble(builder.root, 3)
  return { diagram: builder.build(), outer, inner, target, inaccessible }
}

function withoutNode(diagram: Diagram, nodeId: string): Diagram {
  const nodes: Record<string, DiagramNode> = Object.fromEntries(
    Object.entries(diagram.nodes).filter(([id]) => id !== nodeId),
  )
  const wires: Record<string, Wire> = Object.fromEntries(Object.entries(diagram.wires).map(([id, wire]) => [id, {
    scope: wire.scope,
    endpoints: wire.endpoints.filter((endpoint) => endpoint.node !== nodeId),
  }]))
  return mkDiagram({ root: diagram.root, regions: { ...diagram.regions }, nodes, wires })
}

describe('comprehension dependency authoring', () => {
  it('enumerates strictly enclosing bubbles and imports one usable dependency immutably', () => {
    const host = nestedHost()
    const empty = createComprehensionDependencyState(emptyPattern())

    expect(enclosingComprehensionBinders(host.diagram, host.target)).toEqual([host.outer, host.inner])
    const added = addComprehensionBoundOccurrence(empty, host.diagram, host.target, host.outer)

    expect(empty.dependencies).toEqual([])
    expect(added.state).not.toBe(empty)
    expect(Object.isFrozen(added.state)).toBe(true)
    expect(Object.isFrozen(added.state.dependencies)).toBe(true)
    expect(added.state.dependencies).toEqual([[added.proxy, host.outer]])
    expect(added.state.pattern.diagram.regions[added.proxy]).toEqual({
      kind: 'bubble', parent: added.state.pattern.diagram.root, arity: 1,
    })
    expect(added.state.pattern.diagram.nodes[added.node]).toEqual({
      kind: 'atom', region: added.proxy, binder: added.proxy,
    })
    expect(materializeComprehensionDependencies(added.state, host.diagram, host.target))
      .toEqual([[added.proxy, host.outer]])
  })

  it('orders nested dependencies by host ancestry regardless of import sequence', () => {
    const host = nestedHost()
    const firstOuter = importComprehensionDependency(
      createComprehensionDependencyState(emptyPattern()), host.diagram, host.target, host.outer,
    )
    const thenInner = importComprehensionDependency(
      firstOuter, host.diagram, host.target, host.inner,
    )
    const firstInner = importComprehensionDependency(
      createComprehensionDependencyState(emptyPattern()), host.diagram, host.target, host.inner,
    )
    const thenOuter = importComprehensionDependency(
      firstInner, host.diagram, host.target, host.outer,
    )

    for (const imported of [thenInner, thenOuter]) {
      const withOuter = addComprehensionBoundOccurrence(
        imported, host.diagram, host.target, host.outer,
      ).state
      const state = addComprehensionBoundOccurrence(
        withOuter, host.diagram, host.target, host.inner,
      ).state
      expect(state.dependencies.map(([, target]) => target)).toEqual([host.outer, host.inner])
      const [outerProxy, innerProxy] = state.dependencies.map(([proxy]) => proxy)
      expect(state.pattern.diagram.regions[outerProxy!]).toMatchObject({
        kind: 'bubble', parent: state.pattern.diagram.root,
      })
      expect(state.pattern.diagram.regions[innerProxy!]).toMatchObject({
        kind: 'bubble', parent: outerProxy,
      })
      validateComprehensionDependencies(state, host.diagram, host.target)
    }
  })

  it('deduplicates repeated imports by stable proxy identity', () => {
    const host = nestedHost()
    const empty = createComprehensionDependencyState(emptyPattern())
    const once = importComprehensionDependency(empty, host.diagram, host.target, host.inner)
    const twice = importComprehensionDependency(once, host.diagram, host.target, host.inner)
    const first = addComprehensionBoundOccurrence(twice, host.diagram, host.target, host.inner)
    const second = addComprehensionBoundOccurrence(first.state, host.diagram, host.target, host.inner)

    expect(twice).toBe(once)
    expect(second.proxy).toBe(first.proxy)
    expect(second.state.dependencies).toHaveLength(1)
    expect(Object.values(second.state.pattern.diagram.nodes).filter(
      (node) => node.kind === 'atom' && node.binder === first.proxy,
    )).toHaveLength(2)
  })

  it('moves existing root content into the effective body while boundary wires remain root-scoped', () => {
    const host = nestedHost()
    const patternBuilder = new DiagramBuilder()
    const existingRegion = patternBuilder.cut(patternBuilder.root)
    const boundaryNode = patternBuilder.termNode(patternBuilder.root, p('\\x. x'))
    const bodyNode = patternBuilder.termNode(patternBuilder.root, p('\\y. y'))
    const boundaryWire = patternBuilder.wire(patternBuilder.root, [
      { node: boundaryNode, port: { kind: 'output' } },
    ])
    const bodyWire = patternBuilder.wire(patternBuilder.root, [
      { node: bodyNode, port: { kind: 'output' } },
    ])
    const pattern = mkDiagramWithBoundary(patternBuilder.build(), [boundaryWire])

    const imported = importComprehensionDependency(
      createComprehensionDependencyState(pattern), host.diagram, host.target, host.inner,
    )
    const proxy = imported.dependencies[0]![0]

    expect(imported.pattern.diagram.regions[existingRegion]).toMatchObject({ parent: proxy })
    expect(imported.pattern.diagram.nodes[boundaryNode]).toMatchObject({ region: proxy })
    expect(imported.pattern.diagram.nodes[bodyNode]).toMatchObject({ region: proxy })
    expect(imported.pattern.diagram.wires[boundaryWire]).toMatchObject({ scope: imported.pattern.diagram.root })
    expect(imported.pattern.diagram.wires[bodyWire]).toMatchObject({ scope: proxy })
  })

  it('adds an outer proxy around an existing inner-bound body occurrence without moving it out of the body', () => {
    const host = nestedHost()
    const inner = addComprehensionBoundOccurrence(
      createComprehensionDependencyState(emptyPattern()), host.diagram, host.target, host.inner,
    )

    const importedOuter = importComprehensionDependency(
      inner.state, host.diagram, host.target, host.outer,
    )
    const completed = addComprehensionBoundOccurrence(
      importedOuter, host.diagram, host.target, host.outer,
    ).state
    expect(completed.dependencies.map(([, target]) => target)).toEqual([host.outer, host.inner])
    expect(completed.pattern.diagram.regions[inner.proxy]).toMatchObject({
      kind: 'bubble', parent: completed.dependencies[0]![0],
    })
    expect(completed.pattern.diagram.nodes[inner.node]).toEqual({
      kind: 'atom', region: inner.proxy, binder: inner.proxy,
    })
    validateComprehensionDependencies(completed, host.diagram, host.target)
  })

  it('refuses binders that do not strictly enclose the instantiation target', () => {
    const host = nestedHost()
    const empty = createComprehensionDependencyState(emptyPattern())

    expect(() => importComprehensionDependency(
      empty, host.diagram, host.target, host.inaccessible,
    )).toThrow(/must properly enclose/)
    expect(() => importComprehensionDependency(
      empty, host.diagram, host.target, host.target,
    )).toThrow(/must properly enclose/)
  })

  it('maps a requested pre-import body to the new effective body during authoritative selected import', () => {
    const hostBuilder = new DiagramBuilder()
    const outer = hostBuilder.bubble(hostBuilder.root, 0)
    const inner = hostBuilder.bubble(outer, 0)
    const target = hostBuilder.bubble(inner, 0)
    const selectedAtom = hostBuilder.atom(target, inner)
    const host = hostBuilder.build()
    const selection = mkSelection(host, {
      region: target, regions: [], nodes: [selectedAtom], wires: [],
    })
    const outerOccurrence = addComprehensionBoundOccurrence(
      createComprehensionDependencyState(emptyPattern()), host, target, outer,
    )

    const unrelatedWithCoincidentalIds = mkDiagram({
      root: host.root,
      regions: { ...host.regions },
      nodes: { ...host.nodes },
      wires: { ...host.wires },
    })
    expect(() => mergeSelectedComprehensionDependencies(
      outerOccurrence.state, host, target, unrelatedWithCoincidentalIds, selection, outerOccurrence.proxy,
    )).toThrow(/exact source/)

    const merged = mergeSelectedComprehensionDependencies(
      outerOccurrence.state, host, target, host, selection, outerOccurrence.proxy,
    )
    expect(merged.state.dependencies.map(([, hostTarget]) => hostTarget)).toEqual([outer, inner])
    const innerProxy = merged.state.dependencies[1]![0]
    expect(merged.state.pattern.diagram.nodes[merged.introduced[0]!]).toEqual({
      kind: 'atom', region: innerProxy, binder: innerProxy,
    })
    expect(merged.state.pattern.diagram.nodes[outerOccurrence.node]).toEqual({
      kind: 'atom', region: innerProxy, binder: outerOccurrence.proxy,
    })
    validateComprehensionDependencies(merged.state, host, target)
  })

  it('prunes dead dependencies and promotes surviving content to the repaired prefix body', () => {
    const host = nestedHost()
    const outer = addComprehensionBoundOccurrence(
      createComprehensionDependencyState(emptyPattern()), host.diagram, host.target, host.outer,
    )
    const inner = addComprehensionBoundOccurrence(
      outer.state, host.diagram, host.target, host.inner,
    )
    const edited = mkDiagramWithBoundary(
      withoutNode(inner.state.pattern.diagram, inner.node), inner.state.pattern.boundary,
    )

    const reconciled = reconcileComprehensionDependencies(
      inner.state, edited, host.diagram, host.target,
    )
    expect(reconciled.dependencies).toEqual([[outer.proxy, host.outer]])
    expect(reconciled.pattern.diagram.regions[inner.proxy]).toBeUndefined()
    expect(reconciled.pattern.diagram.nodes[outer.node]).toMatchObject({
      kind: 'atom', region: outer.proxy, binder: outer.proxy,
    })
    validateComprehensionDependencies(reconciled, host.diagram, host.target)
  })

  it('refuses mutation or removal of a proxy while a bound occurrence still uses it', () => {
    const host = nestedHost()
    const added = addComprehensionBoundOccurrence(
      createComprehensionDependencyState(emptyPattern()), host.diagram, host.target, host.outer,
    )

    expect(() => assertComprehensionProxyEditable(added.state, added.proxy))
      .toThrow(/still used/)

    const diagram = added.state.pattern.diagram
    const changedArity = mkDiagramWithBoundary(mkDiagram({
      root: diagram.root,
      regions: { ...diagram.regions, [added.proxy]: { kind: 'bubble', parent: diagram.root, arity: 2 } },
      nodes: { ...diagram.nodes },
      wires: {
        ...diagram.wires,
        extra: { scope: added.proxy, endpoints: [{ node: added.node, port: { kind: 'arg', index: 1 } }] },
      },
    }), added.state.pattern.boundary)
    expect(() => reconcileComprehensionDependencies(
      added.state, changedArity, host.diagram, host.target,
    )).toThrow(/still-used proxy.*mutated/)

    const changedParent = 'edited-parent'
    const reparented = mkDiagramWithBoundary(mkDiagram({
      root: diagram.root,
      regions: {
        ...diagram.regions,
        [changedParent]: { kind: 'cut', parent: diagram.root },
        [added.proxy]: { kind: 'bubble', parent: changedParent, arity: 1 },
      },
      nodes: { ...diagram.nodes },
      wires: { ...diagram.wires },
    }), added.state.pattern.boundary)
    expect(() => reconcileComprehensionDependencies(
      added.state, reparented, host.diagram, host.target,
    )).toThrow(/still-used proxy.*mutated/)
  })
})
