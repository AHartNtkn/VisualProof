import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { applyErasure } from '../../../src/kernel/rules/erasure'
import { applyWireSever } from '../../../src/kernel/rules/wire-quantifier'

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

    const severed = applyWireSever(diagram, {
      wire,
      keep: [{ node: first, port: { kind: 'arg', index: 0 } }],
    })

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

    const severed = applyWireSever(diagram, {
      wire,
      keep: [{ node: first, port: { kind: 'arg', index: 0 } }],
    })
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

    expect(() => applyWireSever(diagram, {
      wire,
      keep: [],
    }))
      .toThrowError(/severing a wire requires a positive scope; 'r1' is negative/)
  })

  it('rejects keep entries that are not endpoints of the wire', () => {
    const builder = new DiagramBuilder()
    const node = builder.ref(builder.root, 'P', relSig([IOTA]))
    const wire = builder.wire(builder.root, [
      { node, port: { kind: 'arg', index: 0 } },
    ])
    const diagram = builder.build()

    expect(() => applyWireSever(diagram, {
      wire,
      keep: [{ node: 'ghost', port: { kind: 'arg', index: 0 } }],
    })).toThrowError(/'ghost'.*is not an endpoint of wire 'w0'/)
  })
})

describe('generalized wire sever', () => {
  it('severs a relation-signature wire', () => {
    const builder = new DiagramBuilder()
    const sig = relSig([IOTA])
    const headA = builder.atom(builder.root, sig)
    const headB = builder.atom(builder.root, sig)
    const rel = builder.wire(builder.root, [
      { node: headA, port: { kind: 'head' } },
      { node: headB, port: { kind: 'head' } },
    ], sig)
    builder.wire(builder.root, [{ node: headA, port: { kind: 'arg', index: 0 } }])
    builder.wire(builder.root, [{ node: headB, port: { kind: 'arg', index: 0 } }])
    const diagram = builder.build()

    const severed = applyWireSever(diagram, {
      wire: rel,
      keep: [{ node: headA, port: { kind: 'head' } }],
    })

    const fresh = Object.keys(severed.wires).find((id) => diagram.wires[id] === undefined)!
    expect(severed.wires[rel]!.endpoints).toEqual([
      { node: headA, port: { kind: 'head' } },
    ])
    expect(severed.wires[fresh]!.sig).toEqual(sig)
    expect(severed.wires[fresh]!.endpoints).toEqual([
      { node: headB, port: { kind: 'head' } },
    ])
  })

  it('scopes the fresh wire at a chosen deeper region and gates on that region', () => {
    const builder = new DiagramBuilder()
    const cut1 = builder.cut(builder.root)
    const cut2 = builder.cut(cut1)
    const keepNode = builder.ref(builder.root, 'K', relSig([IOTA]))
    const movedNode = builder.ref(cut2, 'M', relSig([IOTA]))
    const wire = builder.wire(builder.root, [
      { node: keepNode, port: { kind: 'arg', index: 0 } },
      { node: movedNode, port: { kind: 'arg', index: 0 } },
    ])
    const diagram = builder.build()

    const severed = applyWireSever(diagram, {
      wire,
      keep: [{ node: keepNode, port: { kind: 'arg', index: 0 } }],
      scope: cut2,
    })
    const fresh = Object.keys(severed.wires).find((id) => diagram.wires[id] === undefined)!
    expect(severed.wires[fresh]!.scope).toBe(cut2)
    expect(severed.wires[wire]!.scope).toBe(builder.root)

    expect(() => applyWireSever(diagram, {
      wire,
      keep: [{ node: keepNode, port: { kind: 'arg', index: 0 } }],
      scope: cut1,
    })).toThrowError(/severing a wire requires a positive scope/)
    expect(() => applyWireSever(diagram, {
      wire,
      keep: [{ node: keepNode, port: { kind: 'arg', index: 0 } }],
      scope: cut1,
    }, 'backward')).not.toThrow()
  })

  it('rejects a chosen scope that does not enclose every moved endpoint', () => {
    const builder = new DiagramBuilder()
    const cut1 = builder.cut(builder.root)
    const cut2 = builder.cut(cut1)
    const keepNode = builder.ref(cut2, 'K', relSig([IOTA]))
    const movedNode = builder.ref(builder.root, 'M', relSig([IOTA]))
    const wire = builder.wire(builder.root, [
      { node: keepNode, port: { kind: 'arg', index: 0 } },
      { node: movedNode, port: { kind: 'arg', index: 0 } },
    ])
    const diagram = builder.build()

    expect(() => applyWireSever(diagram, {
      wire,
      keep: [{ node: keepNode, port: { kind: 'arg', index: 0 } }],
      scope: cut2,
    })).toThrowError(/does not enclose moved endpoint/)
  })
})
