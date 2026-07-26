import { describe, expect, it } from 'vitest'
import { planCopy, revalidateCopy } from '../../src/app/copy-planner'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { EMPTY_PROOF_CONTEXT } from '../../src/kernel/proof/context'
import { UNARY } from '../fixtures/zero-signature'

function iterationFixture() {
  const builder = new DiagramBuilder()
  const target = builder.cut(builder.root)
  const atom = builder.atom(builder.root, UNARY)
  builder.wire(builder.root, [{ node: atom, port: { kind: 'head' } }], UNARY)
  const diagram = builder.build()
  const selection = mkSelection(diagram, {
    region: diagram.root, regions: [], nodes: [atom], wires: [],
  })
  return { diagram, selection, target }
}

describe('copy planning on three-node graphs', () => {
  it('uses extract/splice directly in edit mode', () => {
    const fixture = iterationFixture()
    const plan = planCopy(fixture.diagram, fixture.selection, {
      kind: 'edit',
      diagram: fixture.diagram,
      region: fixture.target,
      at: { x: 12, y: 18 },
    })
    expect(plan.kind).toBe('edit')
    if (plan.kind !== 'edit') return
    expect(plan.introduced).toHaveLength(1)
    expect(plan.result.nodes[plan.introduced[0]!]!.kind).toBe('atom')
  })

  it('emits exactly one ordinary iteration step for proof copy', () => {
    const fixture = iterationFixture()
    const plan = planCopy(fixture.diagram, fixture.selection, {
      kind: 'proof',
      diagram: fixture.diagram,
      region: fixture.target,
      orientation: 'forward',
      ctx: EMPTY_PROOF_CONTEXT,
    })
    expect(plan.kind).toBe('proof')
    if (plan.kind !== 'proof') return
    expect(plan.action.steps).toEqual([{
      rule: 'iteration',
      sel: fixture.selection,
      target: fixture.target,
      retargets: [],
    }])
  })

  it('surfaces the iteration cone gate and rejects stale evidence', () => {
    const builder = new DiagramBuilder()
    const sourceRegion = builder.cut(builder.root)
    const atom = builder.atom(sourceRegion, UNARY)
    builder.wire(sourceRegion, [{ node: atom, port: { kind: 'head' } }], UNARY)
    const diagram = builder.build()
    const selection = mkSelection(diagram, {
      region: sourceRegion, regions: [], nodes: [atom], wires: [],
    })
    const outside = planCopy(diagram, selection, {
      kind: 'proof',
      diagram,
      region: diagram.root,
      orientation: 'forward',
      ctx: EMPTY_PROOF_CONTEXT,
    })
    expect(outside.kind).toBe('refusal')
    if (outside.kind === 'refusal') {
      expect(outside.code).toBe('proof-unavailable')
      expect(outside.message).toMatch(/must lie within the source region/)
    }

    const fixture = iterationFixture()
    const destination = {
      kind: 'edit' as const,
      diagram: fixture.diagram,
      region: fixture.target,
      at: { x: 1, y: 2 },
    }
    const plan = planCopy(fixture.diagram, fixture.selection, destination)
    expect(plan.kind).toBe('edit')
    if (plan.kind !== 'edit') return
    expect(revalidateCopy(plan, fixture.diagram, { ...destination, at: { x: 2, y: 3 } }))
      .toMatchObject({ kind: 'refusal', code: 'stale-destination' })
  })
})
