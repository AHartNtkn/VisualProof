import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagram } from '../../../src/kernel/diagram/diagram'
import { exploreForm } from '../../../src/kernel/diagram/canonical/explore'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'

describe('canonical positional and unordered ports', () => {
  it('materializes every declared reference argument and no head port', () => {
    const builder = new DiagramBuilder()
    const ref = builder.ref(builder.root, 'P', relSig([IOTA, IOTA, IOTA]))
    const diagram = builder.build()
    const ports = Object.values(diagram.wires)
      .flatMap((wire) => wire.endpoints)
      .filter((endpoint) => endpoint.node === ref)
      .map((endpoint) => endpoint.port)

    expect(ports).toEqual([
      { kind: 'arg', index: 0 },
      { kind: 'arg', index: 1 },
      { kind: 'arg', index: 2 },
    ])
    expect(ports.some((port) => port.kind === 'head')).toBe(false)
  })

  it('rejects invalid reference ports and an omitted required argument', () => {
    const base = {
      root: 'r0',
      regions: { r0: { kind: 'sheet' as const } },
      nodes: {
        ref: { kind: 'ref' as const, region: 'r0', defId: 'P', sig: relSig([IOTA]) },
      },
    }

    expect(() => mkDiagram({
      ...base,
      wires: {
        invalid: {
          sig: IOTA,
          endpoints: [{ node: 'ref', port: { kind: 'arg', index: 1 } }],
        },
      },
    })).toThrowError(/non-existent port 'a:1'/)
    expect(() => mkDiagram({
      ...base,
      wires: {
        invalid: {
          sig: relSig([IOTA]),
          endpoints: [{ node: 'ref', port: { kind: 'head' } }],
        },
      },
    })).toThrowError(/non-existent port 'hd'/)
    expect(() => mkDiagram({ ...base, wires: {} }))
      .toThrowError(/port 'a:0'.*not attached/)
  })

  it('keeps ordered reference arguments semantic', () => {
    const make = (swapped: boolean) => {
      const builder = new DiagramBuilder()
      const target = builder.ref(builder.root, 'P', relSig([IOTA, IOTA]))
      const marker = builder.ref(builder.root, 'Marker', relSig([IOTA]))
      builder.wire( [
        { node: marker, port: { kind: 'arg', index: 0 } },
        { node: target, port: { kind: 'arg', index: swapped ? 1 : 0 } },
      ])
      return builder.build()
    }

    expect(exploreForm(make(false))).not.toBe(exploreForm(make(true)))
  })

  it('erases identity storage-index permutations from canonical form', () => {
    const make = (swapped: boolean) => mkDiagram({
      root: 'r0',
      regions: {
        r0: { kind: 'sheet' },
        r1: { kind: 'cut', parent: 'r0' },
        r2: { kind: 'cut', parent: 'r1' },
      },
      nodes: {
        eq: { kind: 'identity', region: 'r2', sig: IOTA, arity: 2 },
        outerPin: { kind: 'identity', region: 'r0', sig: IOTA, arity: 1 },
        innerPin: { kind: 'identity', region: 'r1', sig: IOTA, arity: 1 },
      },
      wires: {
        outer: {
          sig: IOTA,
          endpoints: [{
            node: 'eq',
            port: { kind: 'identity', index: swapped ? 1 : 0 },
          }, { node: 'outerPin', port: { kind: 'identity', index: 0 } }],
        },
        inner: {
          sig: IOTA,
          endpoints: [{
            node: 'eq',
            port: { kind: 'identity', index: swapped ? 0 : 1 },
          }, { node: 'innerPin', port: { kind: 'identity', index: 0 } }],
        },
      },
    })

    expect(exploreForm(make(false))).toBe(exploreForm(make(true)))
  })

  it('reuses already-canonical node and wire objects during validation', () => {
    const builder = new DiagramBuilder()
    builder.ref(builder.root, 'P', relSig([IOTA]))
    const diagram = builder.build()
    const rebuilt = mkDiagram({
      root: diagram.root,
      regions: { ...diagram.regions },
      nodes: { ...diagram.nodes },
      wires: { ...diagram.wires },
    })

    for (const id of Object.keys(diagram.nodes)) {
      expect(rebuilt.nodes[id]).toBe(diagram.nodes[id])
    }
    for (const id of Object.keys(diagram.wires)) {
      expect(rebuilt.wires[id]).toBe(diagram.wires[id])
    }
  })

  it('rejects invalid and missing identity storage indices', () => {
    const identity = {
      root: 'r0',
      regions: { r0: { kind: 'sheet' as const } },
      nodes: {
        eq: { kind: 'identity' as const, region: 'r0', sig: IOTA, arity: 2 },
        aPin: { kind: 'identity' as const, region: 'r0', sig: IOTA, arity: 1 },
        bPin: { kind: 'identity' as const, region: 'r0', sig: IOTA, arity: 1 },
        bPin2: { kind: 'identity' as const, region: 'r0', sig: IOTA, arity: 1 },
      },
    }
    const pinEnd = (node: string) => ({
      node,
      port: { kind: 'identity' as const, index: 0 },
    })
    expect(() => mkDiagram({
      ...identity,
      wires: {
        a: {
          sig: IOTA,
          endpoints: [
            { node: 'eq', port: { kind: 'identity', index: 0 } },
            pinEnd('aPin'),
          ],
        },
        b: {
          sig: IOTA,
          endpoints: [
            { node: 'eq', port: { kind: 'identity', index: 2 } },
            pinEnd('bPin'),
          ],
        },
      },
    })).toThrowError(/non-existent port 'i:2'/)
    expect(() => mkDiagram({
      ...identity,
      wires: {
        a: {
          sig: IOTA,
          endpoints: [
            { node: 'eq', port: { kind: 'identity', index: 0 } },
            pinEnd('aPin'),
          ],
        },
        b: {
          sig: IOTA,
          endpoints: [pinEnd('bPin'), pinEnd('bPin2')],
        },
      },
    })).toThrowError(/port 'i:1'.*not attached/)
  })
})
