import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { exploreForm } from '../../../src/kernel/diagram/canonical/explore'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { EMPTY_PROOF_CONTEXT, verifyTheory } from '../../../src/kernel/proof/context'
import { ProofError } from '../../../src/kernel/proof/error'
import {
  applyStep,
  applyStepWithReceipt,
  replayProof,
  transportBoundary,
  type ProofStep,
} from '../../../src/kernel/proof/step'
import { applyErasure } from '../../../src/kernel/rules/erasure'
import { applyIdentityInsertion } from '../../../src/kernel/rules/identity'

describe('primitive replay', () => {
  it('routes erasure through the direct primitive', () => {
    const builder = new DiagramBuilder()
    const atom = builder.atom(builder.root, relSig([]))
    const diagram = builder.build()
    const selection = mkSelection(diagram, {
      region: diagram.root,
      regions: [],
      nodes: [atom],
      wires: [],
    })

    expect(exploreForm(applyStep(
      diagram,
      { rule: 'erasure', sel: selection },
      EMPTY_PROOF_CONTEXT,
    ))).toBe(exploreForm(applyErasure(diagram, selection)))
  })

  it('does not replay forward-only erasure backward', () => {
    const builder = new DiagramBuilder()
    const atom = builder.atom(builder.root, relSig([]))
    const diagram = builder.build()
    const selection = mkSelection(diagram, {
      region: diagram.root,
      regions: [],
      nodes: [atom],
      wires: [],
    })

    expect(() => applyStep(
      diagram,
      { rule: 'erasure', sel: selection },
      EMPTY_PROOF_CONTEXT,
      'backward',
    )).toThrowError(/backward erasure is not supported/i)
  })

  it('routes identity insertion through the orientation-aware polarity gate', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const left = builder.wire(builder.root, [])
    const right = builder.wire(builder.root, [])
    const diagram = builder.build()
    const step: ProofStep = {
      rule: 'identityInsert',
      region: cut,
      wires: [left, right],
    }

    expect(exploreForm(applyStep(
      diagram,
      step,
      EMPTY_PROOF_CONTEXT,
    ))).toBe(exploreForm(applyIdentityInsertion(
      diagram,
      cut,
      [left, right],
    )))
    expect(() => applyStep(
      diagram,
      step,
      EMPTY_PROOF_CONTEXT,
      'backward',
    )).toThrowError(/backward identity insertion requires a positive region/i)

    const backwardPositive: ProofStep = { ...step, region: diagram.root }
    expect(() => applyStep(
      diagram,
      backwardPositive,
      EMPTY_PROOF_CONTEXT,
      'backward',
    )).not.toThrow()
    expect(() => applyStep(
      diagram,
      backwardPositive,
      EMPTY_PROOF_CONTEXT,
    )).toThrowError(/identity insertion requires a negative region/i)
  })

  it('replays ref and atom spawning with the stored signature authority', () => {
    const definition = mkDiagramWithBoundary(
      new DiagramBuilder().build(),
      [],
    )
    const context = verifyTheory({
      relations: [['Truth', definition]],
      theorems: [],
    })
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const relationWire = builder.relWire(builder.root, relSig([]))
    const diagram = builder.build()
    const steps: ProofStep[] = [
      {
        rule: 'refSpawn',
        region: cut,
        defId: 'Truth',
        sig: relSig([]),
      },
      { rule: 'atomSpawn', region: cut, wire: relationWire },
    ]
    const result = replayProof(diagram, steps, context)

    expect(Object.values(result.nodes).map((node) => node.kind).sort())
      .toEqual(['atom', 'ref'])
  })

})

describe('normalized step receipts', () => {
  it('composes wire-join intent with identity degeneration', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const identity = builder.identity(cut, IOTA, 2)
    const outer = builder.wire(builder.root, [{
      node: identity,
      port: { kind: 'identity', index: 0 },
    }])
    const inner = builder.wire(cut, [{
      node: identity,
      port: { kind: 'identity', index: 1 },
    }])
    const diagram = builder.build()

    const receipt = applyStepWithReceipt(
      diagram,
      {
        rule: 'wireJoin',
        input: { kind: 'iota', a: outer, b: inner },
      },
      EMPTY_PROOF_CONTEXT,
    )

    expect(receipt.result.nodes[identity]).toBeUndefined()
    expect(receipt.result.wires[inner]).toBeUndefined()
    expect(receipt.provenance.image(inner)).toBeUndefined()
    expect(receipt.interface.image(outer)).toBe(outer)
    expect(receipt.interface.image(inner)).toBe(outer)
    expect(transportBoundary(receipt.interface, [inner, outer, inner]))
      .toEqual([outer, outer, outer])
  })

  it('eliminates a grounded relation identity while preserving application and parameter wires', () => {
    const contentBuilder = new DiagramBuilder()
    const body = contentBuilder.ref(
      contentBuilder.root,
      'G',
      relSig([IOTA, IOTA]),
    )
    const formal = contentBuilder.wire(contentBuilder.root, [{
      node: body,
      port: { kind: 'arg', index: 0 },
    }])
    const ambient = contentBuilder.wire(contentBuilder.root, [{
      node: body,
      port: { kind: 'arg', index: 1 },
    }])
    const content = mkDiagramWithBoundary(
      contentBuilder.build(),
      [formal, ambient],
    )
    const builder = new DiagramBuilder()
    const negative = builder.cut(builder.root)
    const application = builder.atom(negative, relSig([IOTA]))
    const argument = builder.wire(builder.root, [{
      node: application,
      port: { kind: 'arg', index: 0 },
    }])
    const relation = builder.wire(negative, [{
      node: application,
      port: { kind: 'head' },
    }], relSig([IOTA]))
    const parameter = builder.wire(builder.root, [])
    const diagram = builder.build()

    const receipt = applyStepWithReceipt(
      diagram,
      {
        rule: 'wireJoin',
        input: {
          kind: 'relation',
          wire: relation,
          content,
          parameters: [parameter],
        },
      },
      EMPTY_PROOF_CONTEXT,
    )

    expect(receipt.result.wires[relation]).toBeUndefined()
    expect(receipt.provenance.image(relation)).toBeUndefined()
    expect(receipt.interface.image(relation)).toBeUndefined()
    expect(receipt.provenance.image(argument)).toBe(argument)
    expect(receipt.interface.image(argument)).toBe(argument)
    expect(receipt.provenance.image(parameter)).toBe(parameter)
    expect(receipt.interface.image(parameter)).toBe(parameter)
  })

  it('backward-grounds a positive-root repeated relation and receipts its collapsed alias', () => {
    const contentBuilder = new DiagramBuilder()
    const repeated = contentBuilder.wire(contentBuilder.root, [])
    const content = mkDiagramWithBoundary(
      contentBuilder.build(),
      [repeated, repeated],
    )
    const builder = new DiagramBuilder()
    const application = builder.atom(builder.root, relSig([IOTA, IOTA]))
    const first = builder.wire(builder.root, [{
      node: application,
      port: { kind: 'arg', index: 0 },
    }])
    const second = builder.wire(builder.root, [{
      node: application,
      port: { kind: 'arg', index: 1 },
    }])
    const relation = builder.wire(builder.root, [{
      node: application,
      port: { kind: 'head' },
    }], relSig([IOTA, IOTA]))
    const diagram = builder.build()

    const receipt = applyStepWithReceipt(
      diagram,
      {
        rule: 'wireJoin',
        input: {
          kind: 'relation',
          wire: relation,
          content,
          parameters: [],
        },
      },
      EMPTY_PROOF_CONTEXT,
      'backward',
    )
    const survivor = [first, second].sort()[0]!

    expect(receipt.allocation).toEqual({
      regions: [],
      nodes: ['identity_0'],
      wires: [],
    })
    expect(receipt.result.nodes.identity_0).toBeUndefined()
    expect(receipt.interface.image(first)).toBe(survivor)
    expect(receipt.interface.image(second)).toBe(survivor)
    expect(receipt.interface.image(relation)).toBeUndefined()
  })

  it('preserves sever boundary identities and gives no source identity to the fresh relation wire', () => {
    const builder = new DiagramBuilder()
    const body = builder.ref(builder.root, 'G', relSig([IOTA, IOTA]))
    const formal = builder.wire(builder.root, [{
      node: body,
      port: { kind: 'arg', index: 0 },
    }])
    const ambient = builder.wire(builder.root, [{
      node: body,
      port: { kind: 'arg', index: 1 },
    }])
    const diagram = builder.build()
    const receipt = applyStepWithReceipt(
      diagram,
      {
        rule: 'wireSever',
        input: {
          kind: 'relation',
          scope: diagram.root,
          occurrences: [{
            sel: {
              region: diagram.root,
              regions: [],
              nodes: [body],
              wires: [],
            },
            args: [formal],
          }],
        },
      },
      EMPTY_PROOF_CONTEXT,
    )
    const quantifier = Object.keys(receipt.result.wires)
      .find((id) => diagram.wires[id] === undefined)!

    expect(receipt.interface.image(formal)).toBe(formal)
    expect(receipt.interface.image(ambient)).toBe(ambient)
    expect(receipt.provenance.image(formal)).toBe(formal)
    expect(receipt.provenance.image(ambient)).toBe(ambient)
    expect(receipt.interface.image(quantifier)).toBeUndefined()
    expect(receipt.provenance.image(quantifier)).toBeUndefined()
  })

  it('maps both root wires when double-cut elimination co-scopes an identity', () => {
    const builder = new DiagramBuilder()
    const outerCut = builder.cut(builder.root)
    const innerCut = builder.cut(outerCut)
    const identity = builder.identity(innerCut, IOTA, 2)
    const first = builder.wire(builder.root, [{
      node: identity,
      port: { kind: 'identity', index: 0 },
    }])
    const second = builder.wire(builder.root, [{
      node: identity,
      port: { kind: 'identity', index: 1 },
    }])
    const diagram = builder.build()

    const receipt = applyStepWithReceipt(
      diagram,
      { rule: 'doubleCutElim', region: outerCut },
      EMPTY_PROOF_CONTEXT,
    )
    const survivor = [first, second].sort()[0]!
    const absorbed = survivor === first ? second : first

    expect(receipt.result.nodes[identity]).toBeUndefined()
    expect(receipt.result.wires[absorbed]).toBeUndefined()
    expect(receipt.provenance.image(absorbed)).toBeUndefined()
    expect(receipt.interface.image(first)).toBe(survivor)
    expect(receipt.interface.image(second)).toBe(survivor)
    expect(transportBoundary(receipt.interface, [second, first, second]))
      .toEqual([survivor, survivor, survivor])
  })

  it('keeps an intentionally erased root wire undefined', () => {
    const builder = new DiagramBuilder()
    const erased = builder.wire(builder.root, [], IOTA)
    const diagram = builder.build()
    const receipt = applyStepWithReceipt(
      diagram,
      { rule: 'vacuousElim', wireId: erased },
      EMPTY_PROOF_CONTEXT,
    )

    expect(receipt.result.wires[erased]).toBeUndefined()
    expect(receipt.provenance.image(erased)).toBeUndefined()
    expect(receipt.interface.image(erased)).toBeUndefined()
    expect(transportBoundary(receipt.interface, [erased])).toBeUndefined()
  })

  it('does not treat fresh result wires as source identities', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const diagram = builder.build()
    const receipt = applyStepWithReceipt(
      diagram,
      { rule: 'vacuousIntro', scope: cut, sig: IOTA },
      EMPTY_PROOF_CONTEXT,
    )
    const fresh = Object.keys(receipt.result.wires)
      .find((wire) => diagram.wires[wire] === undefined)!

    expect(receipt.provenance.image(fresh)).toBeUndefined()
    expect(receipt.interface.image(fresh)).toBeUndefined()
  })
})

describe('replay failure reporting', () => {
  it('names the failing step index and rule', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const atom = builder.atom(cut, relSig([]))
    const diagram = builder.build()
    const selection = mkSelection(diagram, {
      region: cut,
      regions: [],
      nodes: [atom],
      wires: [],
    })

    let caught: unknown
    try {
      replayProof(
        diagram,
        [{ rule: 'erasure', sel: selection }],
        EMPTY_PROOF_CONTEXT,
      )
    } catch (error) {
      caught = error
    }

    expect(caught).toBeInstanceOf(ProofError)
    expect((caught as Error).message)
      .toMatch(/step 0 \(erasure\) failed: erasure requires a positive region/)
  })

  it('rejects an unknown theorem name', () => {
    const diagram = new DiagramBuilder().build()
    expect(() => applyStep(diagram, {
      rule: 'theorem',
      name: 'ghost',
      at: {
        sel: {
          region: diagram.root,
          regions: [],
          nodes: [],
          wires: [],
        },
        args: [],
      },
      direction: 'forward',
    }, EMPTY_PROOF_CONTEXT)).toThrowError(/unknown theorem 'ghost'/)
  })
})
