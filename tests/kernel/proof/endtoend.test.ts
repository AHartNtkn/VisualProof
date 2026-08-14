import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { sameDiagram } from '../../../src/kernel/diagram/canonical/iso'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import {
  EMPTY_PROOF_CONTEXT,
  checkTheorem,
  composeActions,
  loadTheory,
  replayProof,
  singleStepAction,
  theoryToJson,
  verifyTheory,
  type Theorem,
  type Theory,
} from '../../../src/kernel/proof/index'
import { contentEndpoints } from '../../fixtures/pins'

const PROPOSITION = relSig([])

function dropQ(): Theorem {
  const left = new DiagramBuilder()
  const p = left.atom(left.root, PROPOSITION)
  const q = left.atom(left.root, PROPOSITION)
  const boundary = left.wire([
    { node: p, port: { kind: 'head' } },
    { node: q, port: { kind: 'head' } },
  ], PROPOSITION)
  const lhs = left.buildOpen([boundary])

  const right = new DiagramBuilder()
  const rightP = right.atom(right.root, PROPOSITION)
  const rightBoundary = right.wire([{
    node: rightP,
    port: { kind: 'head' },
  }], PROPOSITION)
  const rhs = right.buildOpen([rightBoundary])

  return {
    name: 'dropQ',
    lhs,
    rhs,
    actions: [singleStepAction('erase Q', {
      rule: 'erasure',
      sel: {
        region: lhs.diagram.root,
        regions: [],
        nodes: [q],
        wires: [],
      },
    })],
  }
}

describe('end-to-end bidirectional proof', () => {
  it('derives a double cut from the blank sheet', () => {
    const blank = new DiagramBuilder().build()
    const goalBuilder = new DiagramBuilder()
    const outer = goalBuilder.cut(goalBuilder.root)
    goalBuilder.cut(outer)
    const goal = goalBuilder.build()
    const backwardStart = new DiagramBuilder().build()
    const tail = [singleStepAction('double-cut intro', {
      rule: 'doubleCutIntro',
      sel: mkSelection(backwardStart, {
        region: backwardStart.root,
        regions: [],
        nodes: [],
        wires: [],
      }),
    })]
    const actions = composeActions(
      blank,
      backwardStart,
      tail,
      EMPTY_PROOF_CONTEXT,
    )
    const theorem: Theorem = {
      name: 'blankToDoubleCut',
      lhs: mkDiagramWithBoundary(blank, []),
      rhs: mkDiagramWithBoundary(goal, []),
      actions,
    }

    expect(() => checkTheorem(theorem, EMPTY_PROOF_CONTEXT)).not.toThrow()
  })
})

describe('stored derived rule pipeline', () => {
  it('saves, loads, and applies a theorem natively', () => {
    const theory: Theory = { relations: [], theorems: [dropQ()] }
    const { ctx } = loadTheory(
      JSON.parse(JSON.stringify(theoryToJson(theory))),
    )

    const host = new DiagramBuilder()
    const p = host.atom(host.root, PROPOSITION)
    const q = host.atom(host.root, PROPOSITION)
    const boundary = host.wire([
      { node: p, port: { kind: 'head' } },
      { node: q, port: { kind: 'head' } },
    ], PROPOSITION)
    // Q's head goes when the theorem fires; the pin keeps the line above the
    // two-end floor at the scope it already had.
    host.pin(boundary, host.root)
    const marker = host.atom(host.root, relSig([IOTA]))
    const markerArgument = host.wire([{
      node: marker,
      port: { kind: 'arg', index: 0 },
    }])
    const diagram = host.build()

    const result = replayProof(diagram, [{
      rule: 'theorem',
      name: 'dropQ',
      at: {
        sel: {
          region: diagram.root,
          regions: [],
          nodes: [p, q],
          wires: [],
        },
        args: [boundary],
      },
      direction: 'forward',
    }], ctx)

    // P and the marker survive as content, alongside the pins holding the
    // proposition line and the marker's argument.
    expect(Object.values(result.nodes)
      .filter((node) => node.kind !== 'identity')).toHaveLength(2)
    expect(contentEndpoints(result, boundary)).toHaveLength(1)
    expect(result.wires[markerArgument]).toBeDefined()
  })

  it('rejects a theory file whose proof actions were removed', () => {
    const encoded = JSON.parse(JSON.stringify(theoryToJson({
      relations: [],
      theorems: [dropQ()],
    }))) as { theorems: Array<{ actions: unknown[] }> }
    encoded.theorems[0]!.actions = []

    expect(() => loadTheory(encoded))
      .toThrowError(/does not arrive at the stated right-hand side/)
  })

  it('native theorem application equals its primitive expansion', () => {
    const theorem = dropQ()
    const context = verifyTheory({ relations: [], theorems: [theorem] })
    const host = new DiagramBuilder()
    const p = host.atom(host.root, PROPOSITION)
    const q = host.atom(host.root, PROPOSITION)
    const boundary = host.wire([
      { node: p, port: { kind: 'head' } },
      { node: q, port: { kind: 'head' } },
    ], PROPOSITION)
    // Q's head goes when the theorem fires; the pin keeps the line above the
    // two-end floor at the scope it already had.
    host.pin(boundary, host.root)
    const diagram = host.build()

    const native = replayProof(diagram, [{
      rule: 'theorem',
      name: 'dropQ',
      at: {
        sel: {
          region: diagram.root,
          regions: [],
          nodes: [p, q],
          wires: [],
        },
        args: [boundary],
      },
      direction: 'forward',
    }], context)
    const primitive = replayProof(diagram, [{
      rule: 'erasure',
      sel: {
        region: diagram.root,
        regions: [],
        nodes: [q],
        wires: [],
      },
    }], context)

    expect(sameDiagram(native, primitive)).toBe(true)
  })
})
