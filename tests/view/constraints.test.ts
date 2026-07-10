import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkEngine } from '../../src/view/engine'
import type { Engine } from '../../src/view/engine'
import { commitBodyPositions, probeBodyPositions, projectDragToSemanticFrontier, semanticConflicts } from '../../src/view/constraints'
import { recomputeRegions } from '../../src/view/relax'

function arrange(e: Engine, positions: Readonly<Record<string, { x: number; y: number }>>): void {
  for (const [id, pos] of Object.entries(positions)) e.bodies.get(id)!.pos = pos
  e.frame = { center: { x: 0, y: 0 }, half: 160 }
  recomputeRegions(e)
}

function inverseExpansionScene(nested = false): { e: Engine; moving: string; fixedInside: string; outside: string } {
  const b = new DiagramBuilder()
  const outerCut = b.cut(b.root)
  const home = nested ? b.cut(outerCut) : outerCut
  const fixedInside = b.ref(home, 'fixed', 0)
  const moving = b.ref(home, 'moving', 0)
  const outside = b.ref(b.root, 'outside', 0)
  const e = mkEngine(b.build(), [])
  arrange(e, {
    [fixedInside]: { x: -12, y: 0 },
    [moving]: { x: 8, y: 0 },
    [outside]: { x: 52, y: 0 },
  })
  return { e, moving, fixedInside, outside }
}

describe('semantic drag constraints', () => {
  it('stops a member before its derived cut can expand over an outside node', () => {
    const { e, moving } = inverseExpansionScene()
    expect(semanticConflicts(e)).toEqual([])

    const projection = projectDragToSemanticFrontier(e, new Map([[moving, { x: 48, y: 0 }]]))
    expect(projection.blocked).toBe(true)
    expect(projection.fraction).toBeGreaterThan(0)
    expect(projection.fraction).toBeLessThan(1)
    expect(projection.conflicts.some((c) => c.kind === 'body-region')).toBe(true)

    commitBodyPositions(e, projection.positions)
    expect(semanticConflicts(e)).toEqual([])
  })

  it('applies the same invariant through nested derived cuts', () => {
    const { e, moving } = inverseExpansionScene(true)
    expect(semanticConflicts(e)).toEqual([])
    const projection = projectDragToSemanticFrontier(e, new Map([[moving, { x: 55, y: 0 }]]))
    expect(projection.blocked).toBe(true)
    commitBodyPositions(e, projection.positions)
    expect(semanticConflicts(e)).toEqual([])
  })

  it('prevents direct entry into a foreign cut through the same frontier', () => {
    const b = new DiagramBuilder()
    const rootNode = b.ref(b.root, 'root', 0)
    const cut = b.cut(b.root)
    const cutNode = b.ref(cut, 'inside', 0)
    const e = mkEngine(b.build(), [])
    arrange(e, { [rootNode]: { x: -45, y: 0 }, [cutNode]: { x: 15, y: 0 } })
    expect(semanticConflicts(e)).toEqual([])

    const target = e.regions.get(cut)!.center
    const projection = projectDragToSemanticFrontier(e, new Map([[rootNode, target]]))
    expect(projection.blocked || Math.hypot(projection.positions.get(rootNode)!.x - target.x, projection.positions.get(rootNode)!.y - target.y) > 1).toBe(true)
    commitBodyPositions(e, projection.positions)
    expect(semanticConflicts(e)).toEqual([])
  })

  it('probes candidates transactionally without leaking positions or circles', () => {
    const { e, moving } = inverseExpansionScene()
    const beforePos = { ...e.bodies.get(moving)!.pos }
    const beforeRegions = [...e.regions.entries()]

    expect(probeBodyPositions(e, new Map([[moving, { x: 48, y: 0 }]])).length).toBeGreaterThan(0)
    expect(e.bodies.get(moving)!.pos).toEqual(beforePos)
    expect([...e.regions.entries()]).toEqual(beforeRegions)
  })

  it('accepts compatible movement while other node positions remain fixed', () => {
    const { e, moving, fixedInside, outside } = inverseExpansionScene()
    const fixedBefore = { ...e.bodies.get(fixedInside)!.pos }
    const outsideBefore = { ...e.bodies.get(outside)!.pos }
    const projection = projectDragToSemanticFrontier(e, new Map([[moving, { x: 14, y: 8 }]]))
    expect(projection.blocked).toBe(false)
    commitBodyPositions(e, projection.positions)
    expect(e.bodies.get(fixedInside)!.pos).toEqual(fixedBefore)
    expect(e.bodies.get(outside)!.pos).toEqual(outsideBefore)
    expect(semanticConflicts(e)).toEqual([])
  })
})
