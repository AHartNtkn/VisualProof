import { describe, expect, it } from 'vitest'
import { planCopy } from '../../src/app/copy-planner'
import { CopyDragController } from '../../src/app/interact/copy'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { EMPTY_PROOF_CONTEXT } from '../../src/kernel/proof/context'
import type { PointerSample } from '../../src/app/interact/viewport'
import { UNARY } from '../fixtures/zero-signature'

function pointer(node: string): PointerSample {
  return {
    pointerId: 1,
    button: 0,
    client: { x: 10, y: 12 },
    screen: { x: 10, y: 12 },
    world: { x: 10, y: 12 },
    hit: { kind: 'node', id: node },
    shiftKey: false,
    ctrlKey: false,
    altKey: false,
    metaKey: false,
  }
}

describe('copy interaction handoff', () => {
  it('carries a finite placement point with an edit plan', () => {
    const builder = new DiagramBuilder()
    const node = builder.ref(builder.root, 'UnaryWitness', UNARY)
    const diagram = builder.build()
    const selection = mkSelection(diagram, {
      region: diagram.root, regions: [], nodes: [node], wires: [],
    })
    const plan = planCopy(diagram, selection, {
      kind: 'edit',
      diagram,
      region: diagram.root,
      at: { x: 8, y: 13 },
    })
    expect(plan).toMatchObject({ kind: 'edit', at: { x: 8, y: 13 } })
  })

  it('surfaces the planner outside-descendant-cone refusal on release', () => {
    const builder = new DiagramBuilder()
    const sourceRegion = builder.cut(builder.root)
    const node = builder.ref(sourceRegion, 'UnaryWitness', UNARY)
    const diagram = builder.build()
    const refusals: string[] = []
    const commits: unknown[] = []
    const controller = new CopyDragController({
      active: () => true,
      sourceDiagram: () => diagram,
      sourceSelection: () => [{ kind: 'node', id: node }],
      sourceEngine: () => ({}) as never,
      viewScale: () => 1,
      destination: () => ({
        kind: 'proof',
        diagram,
        region: diagram.root,
        orientation: 'forward',
        ctx: EMPTY_PROOF_CONTEXT,
      }),
      commit: (plan) => { commits.push(plan) },
      refuse: (message) => { refusals.push(message) },
      theme: () => ({}) as never,
    })
    const sample = pointer(node)
    const claim = controller.claim(sample)
    expect(claim).not.toBeNull()
    claim!.move(sample)
    claim!.release(sample, true)

    expect(commits).toEqual([])
    expect(refusals).toEqual([
      expect.stringMatching(/must lie within the source region/),
    ])
  })
})
