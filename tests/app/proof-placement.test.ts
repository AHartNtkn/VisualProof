import { describe, expect, it } from 'vitest'
import { seedReplayPlacements } from '../../src/app/proof-placement'
import { mkReplay, type Replay } from '../../src/app/replay'
import { mkDiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkDiagram, type Diagram } from '../../src/kernel/diagram/diagram'
import { applyAction, introducedNodeIds, singleStepAction } from '../../src/kernel/proof/action'
import { registerTheorem, verifyTheory } from '../../src/kernel/proof/context'
import { IOTA } from '../../src/kernel/diagram/sig'
import { carryOver, mkEngine } from '../../src/view/engine'
import { UNARY, tinyTheory } from '../fixtures/zero-signature'

function renamed(
  diagram: Diagram,
  prefix: string,
  reversedWire?: string,
  swapIdentityIncidences = false,
): Diagram {
  const region = (id: string): string => `${prefix}region_${id}`
  const node = (id: string): string => `${prefix}node_${id}`
  const wire = (id: string): string => `${prefix}wire_${id}`
  return mkDiagram({
    root: region(diagram.root),
    regions: Object.fromEntries(Object.entries(diagram.regions).map(([id, value]) => [
      region(id),
      value.kind === 'sheet'
        ? value
        : { kind: 'cut', parent: region(value.parent) },
    ])),
    nodes: Object.fromEntries(Object.entries(diagram.nodes).map(([id, value]) => [
      node(id),
      { ...value, region: region(value.region) },
    ])),
    wires: Object.fromEntries(Object.entries(diagram.wires).map(([id, value]) => [
      wire(id),
      {
        ...value,
        scope: region(value.scope),
        endpoints: (id === reversedWire
          ? [...value.endpoints].reverse()
          : value.endpoints).map((endpoint) => {
          const sourceNode = diagram.nodes[endpoint.node]!
          const port = swapIdentityIncidences
            && sourceNode.kind === 'identity'
            && endpoint.port.kind === 'identity'
            ? {
                kind: 'identity' as const,
                index: sourceNode.arity - 1 - endpoint.port.index,
              }
            : endpoint.port
          return { ...endpoint, node: node(endpoint.node), port }
        }),
      },
    ])),
  })
}

describe('replay placement reconstruction', () => {
  it('replays the original backward prefix from rhs with backward orientation', () => {
    const rhs = new DiagramBuilder().build()
    const backward = singleStepAction(
      'spawn from rhs',
      {
        rule: 'refSpawn',
        region: rhs.root,
        defId: 'UnaryWitness',
        sig: UNARY,
      },
      [{ introducedNode: 0, x: 34, y: 55 }],
    )
    const ctx = verifyTheory(tinyTheory())
    const afterBackward = applyAction(rhs, backward, ctx, 'backward')
    const introduced = introducedNodeIds(rhs, afterBackward)[0]!
    const body = { pos: { x: 0, y: 0 } }
    const replay = {
      actionCount: 2,
      meetingIndex: 0,
      transitions: [
        {
          half: 'backward',
          action: singleStepAction('later backward action', {
            rule: 'doubleCutIntro',
            sel: { region: rhs.root, regions: [], nodes: [], wires: [] },
          }),
          appliedFrom: afterBackward,
          orientation: 'backward',
        },
        {
          half: 'backward',
          action: backward,
          appliedFrom: rhs,
          orientation: 'backward',
        },
      ],
      diagramAt: (cursor: number) => cursor === 2 ? rhs : afterBackward,
    } as unknown as Replay

    seedReplayPlacements(
      { bodies: new Map([[introduced, body]]) } as never,
      replay,
      1,
      ctx,
    )

    expect(body.pos).toEqual({ x: 34, y: 55 })
  })

  it('transports placement and carried layout to a canonically renamed exact RHS', () => {
    const builder = new DiagramBuilder()
    const negative = builder.cut(builder.root)
    const existing = [
      builder.ref(negative, 'UnaryWitness', UNARY),
      builder.atom(negative, UNARY),
      builder.identity(negative, IOTA, 2),
    ]
    const sharedWire = builder.wire(builder.root, [
      { node: existing[0]!, port: { kind: 'arg', index: 0 } },
      { node: existing[1]!, port: { kind: 'arg', index: 0 } },
      { node: existing[2]!, port: { kind: 'identity', index: 0 } },
    ])
    // A second outer wire keeps the identity semantic (the one-point rule
    // collapses an identity with at most one wire scoped above its region).
    builder.wire(builder.root, [
      { node: existing[2]!, port: { kind: 'identity', index: 1 } },
    ])
    const boundaryWire = builder.wire(builder.root, [])
    const lhsDiagram = builder.build()
    const action = singleStepAction(
      'spawn placed witness',
      {
        rule: 'refSpawn',
        region: negative,
        defId: 'UnaryWitness',
        sig: UNARY,
      },
      [{ introducedNode: 0, x: 101, y: 203 }],
    )
    const base = verifyTheory(tinyTheory())
    const computed = applyAction(lhsDiagram, action, base, 'forward')
    const rhsDiagram = renamed(computed, 'rhs_', sharedWire, true)
    const ctx = registerTheorem(base, {
      name: 'RenamedPlacedRhs',
      lhs: mkDiagramWithBoundary(lhsDiagram, [boundaryWire]),
      rhs: mkDiagramWithBoundary(rhsDiagram, [`rhs_wire_${boundaryWire}`]),
      actions: [action],
    })
    const replay = mkReplay('RenamedPlacedRhs', ctx)
    const theorem = ctx.theorems.get('RenamedPlacedRhs')!
    const registeredComputed = applyAction(
      theorem.lhs.diagram,
      theorem.actions[0]!,
      ctx,
      'forward',
    )
    const displayIso = replay.displayIsoAt(replay.actionCount)!
    const layoutIdentity = replay.layoutIdentityBetween(0, replay.actionCount)!
    const reverseIdentity = replay.layoutIdentityBetween(replay.actionCount, 0)!
    const introduced = introducedNodeIds(theorem.lhs.diagram, registeredComputed)[0]!
    const displayedIntroduced = displayIso.nodes.get(introduced)!
    const displayedExisting = layoutIdentity.nodes.get(existing[0]!)!
    const displayedWire = layoutIdentity.wires.get(sharedWire)!

    expect(displayedIntroduced).not.toBe(introduced)
    expect(displayedExisting).not.toBe(existing[0])
    expect(displayedWire).not.toBe(sharedWire)
    expect(displayIso.wires.get(boundaryWire)).toBe(theorem.rhs.boundary[0])
    expect(reverseIdentity.nodes.get(displayedExisting)).toBe(existing[0])
    expect(reverseIdentity.wires.get(displayedWire)).toBe(sharedWire)

    const previous = mkEngine(theorem.lhs.diagram, theorem.lhs.boundary)
    const frame = { center: { x: 10, y: -6 }, half: 80 }
    previous.frame = frame
    previous.scale = 2
    previous.slotShift = 3
    previous.bodies.get(existing[0]!)!.pos = { x: 30, y: 14 }
    previous.bodies.get(existing[0]!)!.theta = 1.25
    previous.bodies.get(`x:${sharedWire}`)!.pos = { x: 50, y: 34 }
    previous.bodies.get(`x:${sharedWire}`)!.theta = 2.5
    previous.wires.get(sharedWire)!.net.junctions = [
      { x: 70, y: 54 },
      { x: 90, y: 74 },
    ]
    previous.wires.get(sharedWire)!.net.edges = [
      [0, 4], [1, 4], [4, 5], [2, 5], [3, 5],
    ]

    const exactRhs = mkEngine(
      replay.diagramAt(replay.actionCount),
      replay.boundaryAt(replay.actionCount),
    )
    const sourceIdentityBind = previous.wires.get(sharedWire)!.binds
      .find((bind) => bind.body === existing[2])!
    const displayedIdentity = layoutIdentity.nodes.get(existing[2]!)!
    const targetIdentityBind = exactRhs.wires.get(displayedWire)!.binds
      .find((bind) => bind.body === displayedIdentity)!
    expect(sourceIdentityBind.key).not.toBe(targetIdentityBind.key)

    carryOver(previous, exactRhs, layoutIdentity)
    seedReplayPlacements(exactRhs, replay, replay.actionCount, ctx)

    expect(exactRhs.bodies.get(displayedIntroduced)!.pos).toEqual({ x: 101, y: 203 })
    expect(exactRhs.bodies.get(displayedExisting)!.pos).toEqual({ x: 20, y: 4 })
    expect(exactRhs.bodies.get(displayedExisting)!.theta).toBe(1.25)
    expect(exactRhs.bodies.get(`x:${displayedWire}`)!.pos).toEqual({ x: 30, y: 14 })
    expect(exactRhs.bodies.get(`x:${displayedWire}`)!.theta).toBe(2.5)
    expect(exactRhs.wires.get(displayedWire)!.net).toEqual({
      junctions: [{ x: 40, y: 24 }, { x: 50, y: 34 }],
      edges: [[2, 4], [1, 4], [4, 5], [0, 5], [3, 5]],
    })
    expect(exactRhs.frame).toBe(frame)
    expect(exactRhs.scale).toBe(1)
    expect(exactRhs.slotShift).toBe(3)
  })
})
