import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
import { RuleError } from '../../../src/kernel/rules/error'
import { applyWireJoin } from '../../../src/kernel/rules/wire-join'

describe('wire join: structural and signature gates', () => {
  it('refuses an iota wire and a rel(iota) wire, naming both signatures', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const individual = builder.wire(cut, [], IOTA)
    const relation = builder.wire(cut, [], relSig([IOTA]))
    const diagram = builder.build()

    expect(() => applyWireJoin(diagram, individual, relation))
      .toThrowError(/cannot join wires of different signatures: 'i' vs '\(i\)'/)
    expect(() => applyWireJoin(diagram, relation, individual)).toThrow(RuleError)
  })

  it('refuses structurally distinct relational signatures', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const unary = builder.wire(cut, [], relSig([IOTA]))
    const binary = builder.wire(cut, [], relSig([IOTA, IOTA]))
    const diagram = builder.build()

    expect(() => applyWireJoin(diagram, unary, binary))
      .toThrowError(/cannot join wires of different signatures: '\(i\)' vs '\(i,i\)'/)
  })

  it('checks signatures before scope comparability', () => {
    const builder = new DiagramBuilder()
    const firstCut = builder.cut(builder.root)
    const secondCut = builder.cut(builder.root)
    const individual = builder.wire(firstCut, [], IOTA)
    const relation = builder.wire(secondCut, [], relSig([IOTA]))
    const diagram = builder.build()

    expect(() => applyWireJoin(diagram, individual, relation))
      .toThrowError(/cannot join wires of different signatures/)
  })

  it('merges comparable exact-signature wires and re-normalizes affected identity content', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const identity = builder.identity(cut, IOTA, 2)
    const outerNode = builder.ref(builder.root, 'outer', relSig([IOTA]))
    const innerNode = builder.ref(cut, 'inner', relSig([IOTA]))
    const outer = builder.wire(builder.root, [
      { node: identity, port: { kind: 'identity', index: 0 } },
      { node: outerNode, port: { kind: 'arg', index: 0 } },
    ])
    const inner = builder.wire(cut, [
      { node: identity, port: { kind: 'identity', index: 1 } },
      { node: innerNode, port: { kind: 'arg', index: 0 } },
    ])
    const diagram = builder.build()
    expect(diagram.nodes[identity]).toBeDefined()

    const joined = applyWireJoin(diagram, outer, inner)

    expect(joined.wires[outer]).toBeDefined()
    expect(joined.wires[inner]).toBeUndefined()
    expect(joined.wires[outer]!.endpoints).toEqual(expect.arrayContaining([
      { node: outerNode, port: { kind: 'arg', index: 0 } },
      { node: innerNode, port: { kind: 'arg', index: 0 } },
    ]))
    expect(joined.nodes[identity]).toBeUndefined()
  })
})
