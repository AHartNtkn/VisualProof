import { describe, expect, it } from 'vitest'
import type { GameTree, GameWorld } from '../../src/game/model'
import { gameSession, publishTreeChange, type TreeChange } from '../../src/game/session'
import { completeBranchCutting } from '../../src/game/tools'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import type { Diagram } from '../../src/kernel/diagram/diagram'
import { snapshotFromDiagram } from '../../src/game/diagram-snapshot'
import { sameDiagram } from '../../src/kernel/diagram/canonical/iso'
import { extractSubgraph } from '../../src/kernel/diagram/subgraph/extract'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { derivedScope } from '../../src/kernel/diagram/regions'
import { IOTA } from '../../src/kernel/diagram/sig'

const blankDiagram = new DiagramBuilder().build()

const largeBuilder = new DiagramBuilder()
const outerRegion = largeBuilder.cut(largeBuilder.root)
const nestedRegion = largeBuilder.cut(outerRegion)
largeBuilder.point(nestedRegion)
const largeDiagram = largeBuilder.build()

function tree(id: string, diagram: Diagram): GameTree {
  return {
    id,
    snapshot: snapshotFromDiagram(diagram),
    placement: { x: 0, z: -20, yaw: 0 },
  }
}

function worldWithTree(id: string, diagram: Diagram): GameWorld {
  return {
    slot: { id: 'slot-a', name: 'Slot A', updatedAtMs: 0 },
    camera: { position: { x: 0, y: 1.7, z: 0 }, yaw: 0, pitch: 0 },
    trees: new Map([[id, tree(id, diagram)]]),
    progress: {
      reputation: 0,
      orders: new Map([['starter-double-cut', { kind: 'pending' }]]),
      tutorialsEnabled: true,
      completedTutorialMilestones: new Set(),
      acquiredToolIds: new Set(),
    },
  }
}

function newRegions(before: Diagram, after: Diagram): string[] {
  return Object.keys(after.regions).filter((id) => before.regions[id] === undefined)
}

function treeValues(trees: ReadonlyMap<string, GameTree>): readonly {
  readonly id: string
  readonly diagramJson: string
  readonly placement: GameTree['placement']
}[] {
  return [...trees.values()].map((entry) => ({
    id: entry.id,
    diagramJson: entry.snapshot.json,
    placement: entry.placement,
  }))
}

describe('game tool session', () => {
  it('rejects deriving a deliverable proposition from a cutting whose tree has changed', () => {
    // Catches delivery citing the tree snapshot captured by a stale cutting.
    const session = gameSession(worldWithTree('large', largeDiagram).trees)
    const source = session.trees.get('large')!
    const cutting = completeBranchCutting(source, source.snapshot.diagram.root)
    const changed = session.planDoubleCut({
      treeId: 'large',
      entity: { kind: 'branch', key: 'root', region: source.snapshot.diagram.root, polarity: 0, pts: [] },
      distance: 12,
    })
    session.commit(session.prepare(changed))

    expect(() => session.propositionForDelivery(cutting)).toThrow(/changed since cutting was taken/)
    expect(session.trees.get('large')).toBe(changed.after)
  })

  it('plans a complete tree mutation without publishing it', () => {
    const session = gameSession(worldWithTree('large', largeDiagram).trees)
    const before = session.trees.get('large')!

    const mutation = session.planDoubleCut({
      treeId: 'large',
      entity: {
        kind: 'branch', key: 'branch', region: nestedRegion,
        polarity: 0, pts: [],
      },
      distance: 12,
    })

    expect(session.trees.get('large')).toBe(before)
    expect(mutation.kind).toBe('update')
    if (mutation.kind !== 'update') throw new Error('expected update')
    expect(mutation.before).toBe(before)
    expect(mutation.after).toMatchObject({ id: 'large', placement: before.placement })
    expect(mutation.after.snapshot).not.toBe(before.snapshot)
  })

  it('spawns a real empty double cut on the pointed branch of any generic tree', () => {
    const session = gameSession(worldWithTree('large', largeDiagram).trees)
    const before = session.trees.get('large')!
    const mutation = session.planDoubleCut({
      treeId: 'large',
      entity: {
        kind: 'branch', key: 'drawing-key-unrelated-to-region', region: nestedRegion,
        polarity: 0, pts: [],
      },
      distance: 12,
    })

    expect(mutation.kind).toBe('update')
    if (mutation.kind !== 'update') throw new Error('expected update')
    expect(Object.keys(mutation.after.snapshot.diagram.regions)).toHaveLength(
      Object.keys(largeDiagram.regions).length + 2,
    )
    const outer = newRegions(mutation.before.snapshot.diagram, mutation.after.snapshot.diagram).find((id) => {
      const region = mutation.after.snapshot.diagram.regions[id]!
      return region.kind === 'cut' && region.parent === nestedRegion
    })!
    const inner = newRegions(mutation.before.snapshot.diagram, mutation.after.snapshot.diagram).find((id) => {
      const region = mutation.after.snapshot.diagram.regions[id]!
      return region.kind === 'cut' && region.parent === outer
    })!
    expect(mutation.after.snapshot.diagram.regions[inner]).toEqual({ kind: 'cut', parent: outer })
    expect(mutation.after.snapshot.json).toBe(snapshotFromDiagram(mutation.after.snapshot.diagram).json)
    expect(session.trees.get('large')).toBe(before)

    session.commit(session.prepare(mutation))
    expect(treeValues(session.trees)).toEqual([{
      id: 'large',
      diagramJson: mutation.after.snapshot.json,
      placement: { x: 0, z: -20, yaw: 0 },
    }])
  })

  it('rejects a stale mutation without replacing the current tree', () => {
    const session = gameSession(worldWithTree('large', largeDiagram).trees)
    const first = session.planDoubleCut({
      treeId: 'large',
      entity: { kind: 'branch', key: 'first', region: nestedRegion, polarity: 0, pts: [] },
      distance: 12,
    })
    const stale = session.planDoubleCut({
      treeId: 'large',
      entity: { kind: 'branch', key: 'stale', region: nestedRegion, polarity: 0, pts: [] },
      distance: 12,
    })
    const prepared = session.prepare(first)
    session.commit(prepared)
    session.commit(prepared)

    expect(() => session.prepare(stale)).toThrow(/changed since change was planned/)
    expect(session.trees.get('large')).toBe(first.after)
  })

  it('rejects stale publication before renderer preparation or save acceptance', () => {
    const session = gameSession(worldWithTree('large', largeDiagram).trees)
    const pointed = {
      treeId: 'large',
      entity: {
        kind: 'branch' as const, key: 'branch', region: nestedRegion,
        polarity: 0 as const, pts: [],
      },
      distance: 12,
    }
    const stale = session.planDoubleCut(pointed)
    const current = session.planDoubleCut(pointed)
    session.commit(session.prepare(current))
    const effects: string[] = []

    expect(() => publishTreeChange(session, stale, {
      prepareTreeChange() { effects.push('renderer-prepare'); return {} },
      commitTreeChange() { effects.push('renderer-commit') },
      discardTreeChange() { effects.push('renderer-discard') },
    }, () => { effects.push('save-accept') })).toThrow(/changed since change was planned/)
    expect(effects).toEqual([])
    expect(session.trees.get('large')).toBe(current.after)
  })

  it('publishes the session after save acceptance and before renderer commit', () => {
    const session = gameSession(worldWithTree('large', largeDiagram).trees)
    const mutation = session.planDoubleCut({
      treeId: 'large',
      entity: {
        kind: 'branch', key: 'branch', region: nestedRegion,
        polarity: 0, pts: [],
      },
      distance: 12,
    })
    const effects: string[] = []

    publishTreeChange(session, mutation, {
      prepareTreeChange() { effects.push('renderer-prepare'); return {} },
      commitTreeChange() {
        expect(session.trees.get('large')).toBe(mutation.after)
        effects.push('renderer-commit')
      },
      discardTreeChange() { effects.push('renderer-discard') },
    }, () => {
      expect(session.trees.get('large')).toBe(mutation.before)
      effects.push('save-accept')
    })

    expect(effects).toEqual(['renderer-prepare', 'save-accept', 'renderer-commit'])
  })

  it('preserves a save acceptance error and releases session preparation when renderer cleanup fails', () => {
    const session = gameSession(worldWithTree('large', largeDiagram).trees)
    const pointed = {
      treeId: 'large',
      entity: {
        kind: 'branch' as const, key: 'branch', region: nestedRegion,
        polarity: 0 as const, pts: [],
      },
      distance: 12,
    }
    const mutation = session.planDoubleCut(pointed)
    const acceptanceError = new Error('writer disposed')

    expect(() => publishTreeChange(session, mutation, {
      prepareTreeChange() { return {} },
      commitTreeChange() {},
      discardTreeChange() { throw new Error('renderer cleanup failed') },
    }, () => { throw acceptanceError })).toThrow(acceptanceError)
    expect(session.trees.get('large')).toBe(mutation.before)

    expect(() => publishTreeChange(session, mutation, {
      prepareTreeChange() { return {} },
      commitTreeChange() {},
      discardTreeChange() {},
    }, () => {})).not.toThrow()
    expect(session.trees.get('large')).toBe(mutation.after)
  })

  it('leaves an inserted tree unpublished when renderer preparation fails', () => {
    // Catches insertion publication retaining a prepared session after renderer preparation rejects.
    const source = tree('source', largeDiagram)
    const session = gameSession(new Map([[source.id, source]]), () => 'tree-copy')
    const insertion = session.planDuplicate(
      completeBranchCutting(source, source.snapshot.diagram.root),
      { x: 8, z: -9, yaw: 0.4 },
    )
    const preparationError = new Error('renderer could not prepare insertion')
    const effects: string[] = []

    expect(() => publishTreeChange(session, insertion, {
      prepareTreeChange() { effects.push('renderer-prepare'); throw preparationError },
      commitTreeChange() { effects.push('renderer-commit') },
      discardTreeChange() { effects.push('renderer-discard') },
    }, () => { effects.push('save-accept') })).toThrow(preparationError)

    expect(effects).toEqual(['renderer-prepare'])
    expect(session.trees.has(insertion.treeId)).toBe(false)
    expect(() => session.prepare(insertion)).not.toThrow()
  })

  it('preserves insertion writer rejection when renderer cleanup also fails', () => {
    // Catches insertion cleanup masking the writer rejection or publishing the inserted tree.
    const source = tree('source', largeDiagram)
    const session = gameSession(new Map([[source.id, source]]), () => 'tree-copy')
    const insertion = session.planDuplicate(
      completeBranchCutting(source, source.snapshot.diagram.root),
      { x: 8, z: -9, yaw: 0.4 },
    )
    const writerError = new Error('insert writer rejected')
    const effects: string[] = []

    expect(() => publishTreeChange(session, insertion, {
      prepareTreeChange() { effects.push('renderer-prepare'); return {} },
      commitTreeChange() { effects.push('renderer-commit') },
      discardTreeChange() {
        effects.push('renderer-discard')
        throw new Error('renderer insertion cleanup failed')
      },
    }, () => {
      effects.push('save-accept')
      throw writerError
    })).toThrow(writerError)

    expect(effects).toEqual(['renderer-prepare', 'save-accept', 'renderer-discard'])
    expect(session.trees.has(insertion.treeId)).toBe(false)
    expect(() => session.prepare(insertion)).not.toThrow()
  })

  it('rejects non-branches and unknown trees without mutation', () => {
    const session = gameSession(worldWithTree('tree-a', blankDiagram).trees)
    const beforeTrees = treeValues(session.trees)
    expect(() => session.planDoubleCut({
      treeId: 'tree-a',
      entity: { kind: 'ring', key: 'r:n0', node: 'n0', headWire: null, pts: [] },
      distance: 5,
    })).toThrow(/branch/)
    expect(() => session.planDoubleCut({
      treeId: 'missing',
      entity: { kind: 'branch', key: 'anything', region: 'r0', polarity: 0, pts: [] },
      distance: 5,
    })).toThrow(/unknown tree/)
    expect(treeValues(session.trees)).toEqual(beforeTrees)
  })

  it('plans legal same-tree subtree iteration while preserving its source tree', () => {
    const builder = new DiagramBuilder()
    const sourceRegion = builder.cut(builder.root)
    builder.point(sourceRegion)
    const targetRegion = builder.cut(builder.root)
    const source = tree('source', builder.build())
    const session = gameSession(new Map([[source.id, source]]))
    const cutting = completeBranchCutting(source, sourceRegion)

    const change = session.planIteration(cutting, {
      treeId: source.id,
      entity: { kind: 'branch', key: 'target', region: targetRegion, polarity: 1, pts: [] },
      distance: 1,
    })

    expect(change.kind).toBe('update')
    expect(session.trees.get(source.id)).toBe(source)
    expect(change.after).not.toBe(source)
    expect(Object.keys(change.after.snapshot.diagram.nodes)).toHaveLength(2)
  })

  it('requires a whole tree for cross-tree iteration', () => {
    const sourceBuilder = new DiagramBuilder()
    const sourceRegion = sourceBuilder.cut(sourceBuilder.root)
    sourceBuilder.point(sourceRegion)
    const source = tree('source', sourceBuilder.build())
    const target = tree('target', blankDiagram)
    const session = gameSession(new Map([[source.id, source], [target.id, target]]))

    expect(() => session.planIteration(completeBranchCutting(source, sourceRegion), {
      treeId: target.id,
      entity: { kind: 'branch', key: 'target', region: target.snapshot.diagram.root, polarity: 0, pts: [] },
      distance: 1,
    })).toThrow(/whole tree/)
  })

  it('cites a complete whole tree at a non-root branch without replacing target content', () => {
    const sourceBuilder = new DiagramBuilder()
    const sourceOuter = sourceBuilder.cut(sourceBuilder.root)
    const sourceNested = sourceBuilder.cut(sourceOuter)
    sourceBuilder.point(sourceNested)
    sourceBuilder.identity(sourceBuilder.root, IOTA, 2)
    const source = tree('source', sourceBuilder.build())
    const targetBuilder = new DiagramBuilder()
    const destination = targetBuilder.cut(targetBuilder.root)
    const rootSentinel = targetBuilder.point(targetBuilder.root)
    const destinationSentinel = targetBuilder.point(destination)
    const targetDiagram = targetBuilder.build()
    const target: GameTree = {
      ...tree('target', targetDiagram),
      placement: { x: 13, z: -7, yaw: 0.25 },
    }
    const session = gameSession(new Map([[source.id, source], [target.id, target]]))

    const change = session.planIteration(completeBranchCutting(source, source.snapshot.diagram.root), {
      treeId: target.id,
      entity: { kind: 'branch', key: 'destination', region: destination, polarity: 1, pts: [] },
      distance: 1,
    })
    const after = change.after.snapshot.diagram
    const originalRegions = new Set(Object.keys(targetDiagram.regions))
    const originalNodes = new Set(Object.keys(targetDiagram.nodes))
    const originalWires = new Set(Object.keys(targetDiagram.wires))
    const insertedRoots = Object.entries(after.regions)
      .filter(([id, region]) =>
        !originalRegions.has(id) && region.kind === 'cut' && region.parent === destination,
      )
      .map(([id]) => id)
    const insertedNodeClosure = new Set(Object.keys(after.nodes).filter((id) => !originalNodes.has(id)))
    const insertedNodes = [...insertedNodeClosure]
      .filter((id) => after.nodes[id]!.region === destination)
    const insertedWires = Object.entries(after.wires)
      .filter(([id, wire]) =>
        !originalWires.has(id)
        && derivedScope(after, id) === destination
        && wire.endpoints.every((endpoint) => insertedNodeClosure.has(endpoint.node)),
      )
      .map(([id]) => id)
    const inserted = extractSubgraph(after, mkSelection(after, {
      region: destination,
      regions: insertedRoots,
      nodes: insertedNodes,
      wires: insertedWires,
    })).pattern.diagram

    expect(change.kind).toBe('update')
    expect(change.treeId).toBe(target.id)
    expect(change.after.placement).toEqual({ x: 13, z: -7, yaw: 0.25 })
    expect(session.trees.get(source.id)).toBe(source)
    expect(session.trees.get(target.id)).toBe(target)
    expect(after.regions[destination]).toEqual({ kind: 'cut', parent: 'r0' })
    expect(after.nodes[rootSentinel]).toEqual({
      kind: 'identity', region: 'r0', sig: { kind: 'iota' }, arity: 0,
    })
    expect(after.nodes[destinationSentinel]).toEqual({
      kind: 'identity', region: 'r1', sig: { kind: 'iota' }, arity: 0,
    })
    expect(insertedRoots).toHaveLength(1)
    expect(sameDiagram(inserted, source.snapshot.diagram)).toBe(true)
  })

  it('duplicates a whole tree with an injected fresh identity and requested placement', () => {
    const source = tree('source', largeDiagram)
    const session = gameSession(new Map([[source.id, source]]), () => 'tree-fresh')

    const change = session.planDuplicate(
      completeBranchCutting(source, source.snapshot.diagram.root),
      { x: 8, z: -9, yaw: 0.4 },
    )

    expect(change).toMatchObject({
      kind: 'insert', treeId: 'tree-fresh',
      after: { id: 'tree-fresh', placement: { x: 8, z: -9, yaw: 0.4 } },
    })
    expect(session.trees.get(source.id)).toBe(source)
    expect(session.trees.has('tree-fresh')).toBe(false)
    expect(change.after.snapshot).not.toBe(source.snapshot)
    expect(change.after.snapshot.diagram).not.toBe(source.snapshot.diagram)
    expect(sameDiagram(change.after.snapshot.diagram, source.snapshot.diagram)).toBe(true)
  })

  it('plans a blank sprout at clear ground without publishing it', () => {
    const source = tree('tree-a', largeDiagram)
    const session = gameSession(new Map([[source.id, source]]), () => 'tree-sprout')

    const change = session.planSpawnSprout(
      { x: 8, z: -3, yaw: 0 },
      [{ kind: 'tree', id: source.id, x: 0, z: 0 }],
    )

    expect(change).toMatchObject({
      kind: 'insert', treeId: 'tree-sprout',
      after: { id: 'tree-sprout', placement: { x: 8, z: -3, yaw: 0 } },
    })
    expect(change.after.snapshot.json).toBe(snapshotFromDiagram(blankDiagram).json)
    expect(session.trees.get(source.id)).toBe(source)
    expect(session.trees.has(change.treeId)).toBe(false)

    const prepared = session.prepare(change)
    expect(session.trees.has(change.treeId)).toBe(false)
    session.commit(prepared)
    expect(session.trees.get(change.treeId)).toBe(change.after)
  })

  it('rejects blocked sprout ground without changing session trees', () => {
    const source = tree('tree-a', largeDiagram)
    const session = gameSession(new Map([[source.id, source]]), () => 'tree-sprout')

    expect(() => session.planSpawnSprout(
      { x: 3.999, z: 0, yaw: 0 },
      [{ kind: 'tree', id: source.id, x: 0, z: 0 }],
    )).toThrow(/too close/)
    expect([...session.trees.entries()]).toEqual([[source.id, source]])
  })

  it('rejects subtree duplication, stale cuttings, and generated identity collisions', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const current = tree('source', builder.build())
    const stale = { ...current, snapshot: snapshotFromDiagram(blankDiagram) }
    const placement = { x: 8, z: -9, yaw: 0.4 }

    expect(() => gameSession(new Map([[current.id, current]]), () => 'fresh')
      .planDuplicate(completeBranchCutting(current, cut), placement)).toThrow(/whole tree/)
    expect(() => gameSession(new Map([[current.id, current]]), () => 'fresh')
      .planDuplicate(completeBranchCutting(stale, stale.snapshot.diagram.root), placement))
      .toThrow(/changed since cutting/)
    expect(() => gameSession(new Map([[current.id, current]]))
      .planIteration(completeBranchCutting(stale, stale.snapshot.diagram.root), {
        treeId: current.id,
        entity: { kind: 'branch', key: 'root', region: current.snapshot.diagram.root, polarity: 0, pts: [] },
        distance: 1,
      })).toThrow(/changed since cutting/)
    expect(() => gameSession(new Map([[current.id, current]]), () => current.id)
      .planDuplicate(completeBranchCutting(current, current.snapshot.diagram.root), placement))
      .toThrow(/already exists/)
  })

  it('prepares, discards, and commits both update and insert changes atomically', () => {
    const source = tree('source', largeDiagram)
    const updateSession = gameSession(new Map([[source.id, source]]))
    const update = updateSession.planDoubleCut({
      treeId: source.id,
      entity: { kind: 'branch', key: 'root', region: source.snapshot.diagram.root, polarity: 0, pts: [] },
      distance: 1,
    })
    const preparedUpdate = updateSession.prepare(update)
    updateSession.discard(preparedUpdate)
    expect(updateSession.trees.get(source.id)).toBe(source)
    updateSession.commit(updateSession.prepare(update))
    expect(updateSession.trees.get(source.id)).toBe(update.after)

    const insertSession = gameSession(new Map([[source.id, source]]), () => 'tree-copy')
    const insert = insertSession.planDuplicate(
      completeBranchCutting(source, source.snapshot.diagram.root),
      { x: 8, z: -9, yaw: 0.4 },
    )
    const preparedInsert = insertSession.prepare(insert)
    expect(insertSession.trees.has(insert.treeId)).toBe(false)
    insertSession.discard(preparedInsert)
    expect(insertSession.trees.has(insert.treeId)).toBe(false)
    insertSession.commit(insertSession.prepare(insert))

    expect(insertSession.trees.get(source.id)).toBe(source)
    expect(insertSession.trees.get(insert.treeId)).toBe(insert.after)
    expect(() => insertSession.prepare({
      kind: 'insert', treeId: source.id, after: { ...insert.after, id: source.id },
    } satisfies TreeChange)).toThrow(/already exists/)
  })
})
