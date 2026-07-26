import { describe, expect, it } from 'vitest'
import { applicableActions } from '../../src/app/actions'
import {
  proofConnectionStep,
  relationJoinStep,
  relationSeverStep,
} from '../../src/app/interact/moves'
import { mkDiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { IOTA, relSig } from '../../src/kernel/diagram/sig'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { EMPTY_PROOF_CONTEXT } from '../../src/kernel/proof/context'
import { UNARY } from '../fixtures/zero-signature'

describe('proof move vocabulary', () => {
  it('discovers only structural descriptors', () => {
    const builder = new DiagramBuilder()
    const node = builder.ref(builder.root, 'Unknown', UNARY)
    const diagram = builder.build()
    const selection = mkSelection(diagram, {
      region: diagram.root, regions: [], nodes: [node], wires: [],
    })
    const kinds = applicableActions(diagram, selection, EMPTY_PROOF_CONTEXT)
      .map((action) => action.kind)
    expect(kinds).toContain('erase')
    expect(kinds).toContain('iterate')
    expect(kinds).not.toContain('convert')
    expect(kinds).not.toContain('instantiate')
    expect(kinds).not.toContain('abstract')
  })

  it('constructs direct connection drags only as durable IOTA joins', () => {
    const builder = new DiagramBuilder()
    const negative = builder.cut(builder.root)
    const left = builder.wire(negative, [], IOTA)
    const right = builder.wire(negative, [], IOTA)
    const diagram = builder.build()

    expect(proofConnectionStep(
      diagram,
      { wire: left, endpoint: null },
      { wire: right, endpoint: null },
      'forward',
      0,
    )).toEqual({
      rule: 'wireJoin',
      input: { kind: 'iota', a: left, b: right },
    })
  })

  it('rejects direct relation-wire merges through the kernel IOTA gate', () => {
    const builder = new DiagramBuilder()
    const negative = builder.cut(builder.root)
    const left = builder.wire(negative, [], relSig([]))
    const right = builder.wire(negative, [], relSig([]))
    const diagram = builder.build()

    expect(() => proofConnectionStep(
      diagram,
      { wire: left, endpoint: null },
      { wire: right, endpoint: null },
      'forward',
      0,
    )).toThrowError(/iota wire join requires IOTA wire/)
  })

  it('constructs a checked relation sever step from explicit scope and occurrences', () => {
    const builder = new DiagramBuilder()
    const contentNode = builder.ref(builder.root, 'Content', relSig([]))
    const diagram = builder.build()
    const occurrence = {
      sel: mkSelection(diagram, {
        region: diagram.root,
        regions: [],
        nodes: [contentNode],
        wires: [],
      }),
      args: [],
    }

    expect(relationSeverStep(
      diagram,
      diagram.root,
      [occurrence],
      'forward',
    )).toEqual({
      rule: 'wireSever',
      input: {
        kind: 'relation',
        scope: diagram.root,
        occurrences: [occurrence],
      },
    })
    expect(() => relationSeverStep(
      diagram,
      diagram.root,
      [],
      'forward',
    )).toThrowError('relation wire sever requires at least one occurrence')
  })

  it('constructs a checked relation join step with self-contained content and parameters', () => {
    const builder = new DiagramBuilder()
    const negative = builder.cut(builder.root)
    const application = builder.atom(negative, relSig([]))
    const relation = builder.wire(negative, [{
      node: application,
      port: { kind: 'head' },
    }], relSig([]))
    const diagram = builder.build()
    const content = mkDiagramWithBoundary(new DiagramBuilder().build(), [])

    expect(relationJoinStep(
      diagram,
      relation,
      content,
      [],
      'forward',
    )).toEqual({
      rule: 'wireJoin',
      input: {
        kind: 'relation',
        wire: relation,
        content,
        parameters: [],
      },
    })

    const positiveBuilder = new DiagramBuilder()
    const positiveRelation = positiveBuilder.relWire(
      positiveBuilder.root,
      relSig([]),
    )
    const positive = positiveBuilder.build()
    expect(() => relationJoinStep(
      positive,
      positiveRelation,
      content,
      [],
      'forward',
    )).toThrowError(/relation wire join requires a negative scope/)
  })
})
