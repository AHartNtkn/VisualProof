import { describe, expect, it } from 'vitest'
import type { GameTree, GameWorld } from '../../src/game/model'
import { gameSession, publishTreeMutation } from '../../src/game/session'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import type { Diagram } from '../../src/kernel/diagram/diagram'
import { snapshotFromDiagram } from '../../src/game/diagram-snapshot'

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

    expect(() => session.prepare(stale)).toThrow(/changed since mutation was planned/)
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

    expect(() => publishTreeMutation(session, stale, {
      prepareTreeUpdate() { effects.push('renderer-prepare'); return {} },
      commitTreeUpdate() { effects.push('renderer-commit') },
      discardTreeUpdate() { effects.push('renderer-discard') },
    }, () => { effects.push('save-accept') })).toThrow(/changed since mutation was planned/)
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

    publishTreeMutation(session, mutation, {
      prepareTreeUpdate() { effects.push('renderer-prepare'); return {} },
      commitTreeUpdate() {
        expect(session.trees.get('large')).toBe(mutation.after)
        effects.push('renderer-commit')
      },
      discardTreeUpdate() { effects.push('renderer-discard') },
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

    expect(() => publishTreeMutation(session, mutation, {
      prepareTreeUpdate() { return {} },
      commitTreeUpdate() {},
      discardTreeUpdate() { throw new Error('renderer cleanup failed') },
    }, () => { throw acceptanceError })).toThrow(acceptanceError)
    expect(session.trees.get('large')).toBe(mutation.before)

    expect(() => publishTreeMutation(session, mutation, {
      prepareTreeUpdate() { return {} },
      commitTreeUpdate() {},
      discardTreeUpdate() {},
    }, () => {})).not.toThrow()
    expect(session.trees.get('large')).toBe(mutation.after)
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
})
