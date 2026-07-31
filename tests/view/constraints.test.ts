import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { relSig, IOTA } from '../../src/kernel/diagram/sig'
import { mkEngine } from '../../src/view/engine'
import type { Engine } from '../../src/view/engine'
import { commitBodyPositions, probeBodyPositions, projectDragToSemanticFrontier, semanticConflicts } from '../../src/view/constraints'
import { PACE, recomputeRegions } from '../../src/view/relax'

/** An n-ary relation signature over individuals (ref/atom arity, new sig API). */
const rel = (n: number) => relSig(Array.from({ length: n }, () => IOTA))

/** Penetration of `body` past the SEMANTIC bound of region `rid` (wu): its
    disc crossing the drawn circle. */
function conflictDepth(e: Engine, body: string, rid: string): number {
  const b = e.bodies.get(body)!
  const g = e.regions.get(rid)!
  const need = g.radius + b.discR * e.scale
  return need - Math.hypot(b.pos.x - g.center.x, b.pos.y - g.center.y)
}

function arrange(e: Engine, positions: Readonly<Record<string, { x: number; y: number }>>): void {
  for (const [id, pos] of Object.entries(positions)) e.bodies.get(id)!.pos = pos
  e.frame = { center: { x: 0, y: 0 }, half: 160 }
  recomputeRegions(e)
}

function inverseExpansionScene(nested = false): { e: Engine; moving: string; fixedInside: string; outside: string } {
  const b = new DiagramBuilder()
  const outerCut = b.cut(b.root)
  const home = nested ? b.cut(outerCut) : outerCut
  const fixedInside = b.ref(home, 'fixed', rel(0))
  const moving = b.ref(home, 'moving', rel(0))
  const outside = b.ref(b.root, 'outside', rel(0))
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
    const rootNode = b.ref(b.root, 'root', rel(0))
    const cut = b.cut(b.root)
    const cutNode = b.ref(cut, 'inside', rel(0))
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

  it('a marginal conflict elsewhere in the scene never freezes an unrelated drag', () => {
    // Physics transients can leave sub-wu violations of the semantic bound (a
    // bystander's disc a fraction of a unit across a sibling circle). The
    // frontier must block only what THIS drag introduces or deepens — otherwise
    // one such residual anywhere freezes every drag at fraction 0 (the live-app
    // "mouse stops at a wire" bug: wire physics parked a dot marginally inside
    // a circle and all interaction died).
    const b = new DiagramBuilder()
    const cut = b.cut(b.root)
    const member = b.ref(cut, 'member', rel(0))
    const bystander = b.ref(b.root, 'bystander', rel(0))
    const mover = b.ref(b.root, 'mover', rel(0))
    const e = mkEngine(b.build(), [])
    arrange(e, { [member]: { x: 0, y: 0 }, [bystander]: { x: 60, y: 0 }, [mover]: { x: -90, y: 0 } })
    // park the bystander's disc a hair across the drawn cut circle
    const g = e.regions.get(cut)!
    const by = e.bodies.get(bystander)!
    by.pos = { x: g.center.x + g.radius + by.discR * e.scale - 0.15, y: g.center.y }
    recomputeRegions(e)
    expect(semanticConflicts(e).some((c) => c.kind === 'body-region')).toBe(true)

    const projection = projectDragToSemanticFrontier(e, new Map([[mover, { x: -85, y: 3 }]]))
    expect(projection.blocked).toBe(false)
    commitBodyPositions(e, projection.positions)
    expect(e.bodies.get(mover)!.pos).toEqual({ x: -85, y: 3 })
  })

  it('a drag still cannot deepen a conflict the scene already has', () => {
    const b = new DiagramBuilder()
    const cut = b.cut(b.root)
    const member = b.ref(cut, 'member', rel(0))
    const bystander = b.ref(b.root, 'bystander', rel(0))
    const e = mkEngine(b.build(), [])
    arrange(e, { [member]: { x: 0, y: 0 }, [bystander]: { x: 60, y: 0 } })
    const g = e.regions.get(cut)!
    const by = e.bodies.get(bystander)!
    by.pos = { x: g.center.x + g.radius + by.discR * e.scale - 0.15, y: g.center.y }
    recomputeRegions(e)
    const baseDepth = conflictDepth(e, bystander, cut)
    expect(baseDepth).toBeGreaterThan(0.1)

    // dragging the member toward the bystander expands the derived cut circle
    // over it — the frontier must stop before the penetration deepens
    const projection = projectDragToSemanticFrontier(e, new Map([[member, { x: 20, y: 0 }]]))
    expect(projection.blocked).toBe(true)
    commitBodyPositions(e, projection.positions)
    expect(conflictDepth(e, bystander, cut)).toBeLessThanOrEqual(baseDepth + 0.05)
  })

  it('gap-distance rest contact does not pin a drag at fraction 0 (the hard gate is the SEMANTIC bound)', () => {
    // Settled scenes rest AT the aesthetic gap distance between sibling
    // circles. Dragging a member expands its derived circle, deepening that
    // "contact" by epsilon from the very first micron — if the hard gate
    // included the gap, every such drag would freeze at fraction 0 (the
    // "existential dots randomly stop" bug). The gate must only bind at the
    // semantic boundary: the circles actually meeting.
    const b = new DiagramBuilder()
    const cutA = b.cut(b.root)
    const mA = b.ref(cutA, 'a', rel(0))
    const cutB = b.cut(b.root)
    const mB = b.ref(cutB, 'b', rel(0))
    const e = mkEngine(b.build(), [])
    arrange(e, { [mA]: { x: 0, y: 0 }, [mB]: { x: 100, y: 0 } })
    // park B's circle exactly at the aesthetic gap from A's (a settled rest)
    const gA = e.regions.get(cutA)!
    const gB = e.regions.get(cutB)!
    const restDist = gA.radius + gB.radius + PACE.sibGap * e.scale
    e.bodies.get(mB)!.pos = { x: gA.center.x + restDist, y: gA.center.y }
    recomputeRegions(e)
    expect(semanticConflicts(e)).toEqual([])

    // drag A's member toward B by less than the gap: full progress
    const start = { ...e.bodies.get(mA)!.pos }
    const target = { x: start.x + PACE.sibGap * e.scale * 0.5, y: start.y }
    const projection = projectDragToSemanticFrontier(e, new Map([[mA, target]]))
    commitBodyPositions(e, projection.positions)
    const got = e.bodies.get(mA)!.pos
    expect(Math.hypot(got.x - target.x, got.y - target.y)).toBeLessThan(0.1)
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
