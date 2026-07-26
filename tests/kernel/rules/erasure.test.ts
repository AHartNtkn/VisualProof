import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { applyErasure, applyWireSever } from '../../../src/kernel/rules/erasure'

describe('applyErasure', () => {
  it('removes a selection from a positive region', () => {
    const builder = new DiagramBuilder()
    const node = builder.ref(builder.root, 'outside', relSig([]))
    const cut = builder.cut(builder.root)
    builder.ref(cut, 'inside', relSig([]))
    const diagram = builder.build()
    const selection = mkSelection(diagram, {
      region: diagram.root,
      regions: [],
      nodes: [node],
      wires: [],
    })

    const erased = applyErasure(diagram, selection)

    expect(erased.nodes[node]).toBeUndefined()
    expect(erased.regions[cut]).toBeDefined()
  })

  it('erases whole subtrees from doubly-cut positive regions', () => {
    const builder = new DiagramBuilder()
    const negative = builder.cut(builder.root)
    const positive = builder.cut(negative)
    const child = builder.cut(positive)
    builder.ref(child, 'inside', relSig([]))
    const diagram = builder.build()
    const selection = mkSelection(diagram, {
      region: positive,
      regions: [child],
      nodes: [],
      wires: [],
    })

    const erased = applyErasure(diagram, selection)

    expect(erased.regions[child]).toBeUndefined()
  })

  it('rejects negative regions by name', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const node = builder.ref(cut, 'inside', relSig([]))
    const diagram = builder.build()
    const selection = mkSelection(diagram, {
      region: cut,
      regions: [],
      nodes: [node],
      wires: [],
    })

    expect(() => applyErasure(diagram, selection))
      .toThrowError(/erasure requires a positive region; 'r1' is negative/)
  })

  it('rejects forward-only erasure during backward replay', () => {
    const builder = new DiagramBuilder()
    const node = builder.ref(builder.root, 'outside', relSig([]))
    const diagram = builder.build()
    const selection = mkSelection(diagram, {
      region: diagram.root,
      regions: [],
      nodes: [node],
      wires: [],
    })

    expect(() => applyErasure(diagram, selection, 'backward'))
      .toThrowError(/backward erasure is not supported/i)
  })
})

describe('applyWireSever', () => {
  it('splits endpoints into two wires at the same positive scope', () => {
    const builder = new DiagramBuilder()
    const first = builder.ref(builder.root, 'P', relSig([IOTA]))
    const second = builder.ref(builder.root, 'Q', relSig([IOTA]))
    const wire = builder.wire(builder.root, [
      { node: first, port: { kind: 'arg', index: 0 } },
      { node: second, port: { kind: 'arg', index: 0 } },
    ])
    const diagram = builder.build()

    const severed = applyWireSever(diagram, wire, [
      { node: first, port: { kind: 'arg', index: 0 } },
    ])

    expect(severed.wires[wire]!.endpoints).toEqual([
      { node: first, port: { kind: 'arg', index: 0 } },
    ])
    const fresh = Object.keys(severed.wires).filter((id) => diagram.wires[id] === undefined)
    expect(fresh).toHaveLength(1)
    expect(severed.wires[fresh[0]!]!.endpoints).toEqual([
      { node: second, port: { kind: 'arg', index: 0 } },
    ])
  })

  it('creates the fresh wire at the original nested positive scope', () => {
    const builder = new DiagramBuilder()
    const firstCut = builder.cut(builder.root)
    const positive = builder.cut(firstCut)
    const first = builder.ref(positive, 'P', relSig([IOTA]))
    const second = builder.ref(positive, 'Q', relSig([IOTA]))
    const wire = builder.wire(positive, [
      { node: first, port: { kind: 'arg', index: 0 } },
      { node: second, port: { kind: 'arg', index: 0 } },
    ])
    const diagram = builder.build()

    const severed = applyWireSever(diagram, wire, [
      { node: first, port: { kind: 'arg', index: 0 } },
    ])
    const fresh = Object.keys(severed.wires).find((id) => diagram.wires[id] === undefined)!

    expect(severed.wires[fresh]!.scope).toBe(positive)
    expect(severed.wires[wire]!.scope).toBe(positive)
  })

  it('rejects severing at a negative scope', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const node = builder.ref(cut, 'P', relSig([IOTA]))
    const wire = builder.wire(cut, [
      { node, port: { kind: 'arg', index: 0 } },
    ])
    const diagram = builder.build()

    expect(() => applyWireSever(diagram, wire, []))
      .toThrowError(/severing a wire requires a positive scope; 'r1' is negative/)
  })

  it('rejects keep entries that are not endpoints of the wire', () => {
    const builder = new DiagramBuilder()
    const node = builder.ref(builder.root, 'P', relSig([IOTA]))
    const wire = builder.wire(builder.root, [
      { node, port: { kind: 'arg', index: 0 } },
    ])
    const diagram = builder.build()

    expect(() => applyWireSever(diagram, wire, [
      { node: 'ghost', port: { kind: 'arg', index: 0 } },
    ])).toThrowError(/'ghost'.*is not an endpoint of wire 'w0'/)
  })
})
