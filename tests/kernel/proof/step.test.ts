import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { exploreForm } from '../../../src/kernel/diagram/canonical/explore'
import { derivedScope } from '../../../src/kernel/diagram/regions'
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
import {
  bareWireAssembly,
  bareWireDescription,
} from '../../../src/kernel/rules/identity-rules'

describe('primitive replay', () => {
  it('routes erasure through the direct primitive', () => {
    const builder = new DiagramBuilder()
    const atom = builder.atom(builder.root, relSig([]))
    // The head wire dies with the atom, so its own second end — the pin —
    // belongs in the selection; erasing only the atom would strand it.
    const head = builder.wire( [{ node: atom, port: { kind: 'head' } }], relSig([]))
    const headPin = builder.pin(head, builder.root)
    const diagram = builder.build()
    const selection = mkSelection(diagram, {
      region: diagram.root,
      regions: [],
      nodes: [atom, headPin],
      wires: [head],
    })

    expect(exploreForm(applyStep(
      diagram,
      { rule: 'erasure', sel: selection },
      EMPTY_PROOF_CONTEXT,
    ))).toBe(exploreForm(applyErasure(diagram, selection)))
  })

  it('replays backward erasure only at negative regions', () => {
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
    )).toThrowError(/backward erasure requires a negative region/)
  })

  it('routes identity insertion through the orientation-aware polarity gate', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    // Two bare root-scoped wires: each is a two-point segment, so both are
    // visible inside the cut where the identity is inserted.
    const left = builder.wire( [])
    builder.pin(left, builder.root)
    builder.pin(left, builder.root)
    const right = builder.wire( [])
    builder.pin(right, builder.root)
    builder.pin(right, builder.root)
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
    const defBuilder = new DiagramBuilder()
    const formal = defBuilder.wire( [])
    const definition = defBuilder.buildOpen([formal])
    const context = verifyTheory({
      relations: [['Any', definition]],
      theorems: [],
    })
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const relationWire = builder.relWire( relSig([IOTA]))
    builder.pin(relationWire, builder.root)
    builder.pin(relationWire, builder.root)
    const diagram = builder.build()
    const steps: ProofStep[] = [
      {
        rule: 'refSpawn',
        region: cut,
        defId: 'Any',
        sig: relSig([IOTA]),
      },
      { rule: 'atomSpawn', region: cut, wire: relationWire },
    ]
    const result = replayProof(diagram, steps, context)

    // Both spawns mint a pin at the spawn region for each fresh argument
    // wire, on top of the two pins that made the relational wire bare.
    expect(Object.values(result.nodes).map((node) => node.kind).sort())
      .toEqual(['atom', 'identity', 'identity', 'identity', 'identity', 'ref'])
  })

})

describe('normalized step receipts', () => {
  it('maps an overlapped iteration boundary position to the surviving original wire', () => {
    const builder = new DiagramBuilder()
    const node = builder.atom(builder.root, relSig([IOTA]))
    const wire = builder.wire( [
      { node, port: { kind: 'arg', index: 0 } },
    ])
    const tip = builder.pin(wire, builder.root)
    const diagram = builder.build()
    const sel = mkSelection(diagram, {
      region: diagram.root,
      regions: [],
      nodes: [node, tip],
      wires: [wire],
    })
    const receipt = applyStepWithReceipt(
      diagram,
      { rule: 'iteration', sel, target: diagram.root },
      EMPTY_PROOF_CONTEXT,
    )
    const boundary = mkDiagramWithBoundary(diagram, [wire]).boundary
    const copiedNode = Object.entries(receipt.result.nodes).find(
      ([id, candidate]) =>
        id !== node
        && candidate.kind === 'atom'
        && candidate.region === diagram.root,
    )
    expect(copiedNode).toBeDefined()
    const copiedWire = Object.entries(receipt.result.wires).find(
      ([id, candidate]) =>
        id !== wire
        && derivedScope(receipt.result, id) === diagram.root
        && candidate.endpoints.some(
          (endpoint) =>
            endpoint.node === copiedNode![0]
            && endpoint.port.kind === 'arg'
            && endpoint.port.index === 0,
        ),
    )
    expect(copiedWire).toBeDefined()

    expect(receipt.interface.image(wire)).toBe(wire)
    expect(receipt.interface.image(copiedWire![0])).toBeUndefined()
    expect(transportBoundary(receipt.interface, boundary)).toEqual([wire])
    expect(transportBoundary(receipt.interface, [
      ...boundary,
      copiedWire![0],
    ])).toBeUndefined()
  })

  it('composes wire-join intent over a surviving equating node', () => {
    // The identity sits below both wire scopes; the pins put one quantifier
    // at the sheet and the other in the negative cut the join needs. The
    // node itself persists — the join merges wires, not equalities — so both
    // of its ports end up on the surviving wire as a loop.
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const deep = builder.cut(cut)
    const identity = builder.identity(deep, IOTA, 2)
    const outer = builder.wire( [{
      node: identity,
      port: { kind: 'identity', index: 0 },
    }])
    builder.pin(outer, builder.root)
    const inner = builder.wire( [{
      node: identity,
      port: { kind: 'identity', index: 1 },
    }])
    builder.pin(inner, cut)
    const diagram = builder.build()

    expect(derivedScope(diagram, outer)).toBe(diagram.root)
    expect(derivedScope(diagram, inner)).toBe(cut)

    const receipt = applyStepWithReceipt(
      diagram,
      {
        rule: 'wireJoin',
        input: { a: outer, b: inner },
      },
      EMPTY_PROOF_CONTEXT,
    )

    expect(receipt.result.nodes[identity])
      .toEqual({ kind: 'identity', region: deep, sig: IOTA, arity: 2 })
    expect(receipt.result.wires[inner]).toBeUndefined()
    expect(receipt.result.wires[outer]!.endpoints
      .filter((endpoint) => endpoint.node === identity)).toHaveLength(2)
    expect(derivedScope(receipt.result, outer)).toBe(diagram.root)
    expect(receipt.provenance.image(inner)).toBeUndefined()
    expect(receipt.interface.image(outer)).toBe(outer)
    expect(receipt.interface.image(inner)).toBe(outer)
    expect(transportBoundary(receipt.interface, [inner, outer, inner]))
      .toEqual([outer, outer, outer])
  })

  it('maps both root wires when double-cut elimination lifts a co-scoped identity', () => {
    const builder = new DiagramBuilder()
    const outerCut = builder.cut(builder.root)
    const innerCut = builder.cut(outerCut)
    const identity = builder.identity(innerCut, IOTA, 2)
    const first = builder.wire( [{
      node: identity,
      port: { kind: 'identity', index: 0 },
    }])
    const second = builder.wire( [{
      node: identity,
      port: { kind: 'identity', index: 1 },
    }])
    const diagram = builder.build()

    const receipt = applyStepWithReceipt(
      diagram,
      { rule: 'doubleCutElim', region: outerCut },
      EMPTY_PROOF_CONTEXT,
    )

    // Elimination reparents the inner cut's content two cuts up; the equating
    // node rides along and nothing merges its wires, so both keep their ids
    // and both are now root-scoped.
    expect(receipt.result.nodes[identity])
      .toEqual({ kind: 'identity', region: diagram.root, sig: IOTA, arity: 2 })
    expect(derivedScope(receipt.result, first)).toBe(diagram.root)
    expect(derivedScope(receipt.result, second)).toBe(diagram.root)
    expect(receipt.provenance.image(first)).toBe(first)
    expect(receipt.provenance.image(second)).toBe(second)
    expect(receipt.interface.image(first)).toBe(first)
    expect(receipt.interface.image(second)).toBe(second)
    expect(transportBoundary(receipt.interface, [second, first, second]))
      .toEqual([second, first, second])
  })

  it('keeps an intentionally erased root wire undefined', () => {
    const builder = new DiagramBuilder()
    const erased = builder.wire( [], IOTA)
    builder.pin(erased, builder.root)
    builder.pin(erased, builder.root)
    const diagram = builder.build()
    const receipt = applyStepWithReceipt(
      diagram,
      {
        rule: 'vacuity',
        direction: 'delete',
        assembly: bareWireDescription(diagram, erased),
      },
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
      {
        rule: 'vacuity',
        direction: 'insert',
        assembly: bareWireAssembly('bare', cut, IOTA),
      },
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
