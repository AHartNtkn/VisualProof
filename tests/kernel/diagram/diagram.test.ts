import { describe, expect, it } from 'vitest'
import {
  mkDiagram,
  portKey,
  portSig,
  requiredPorts,
  type DiagramNode,
} from '../../../src/kernel/diagram/diagram'
import { derivedScope } from '../../../src/kernel/diagram/regions'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'

describe('diagram node and port vocabulary', () => {
  it('has canonical keys for arg, head, and identity ports', () => {
    expect(portKey({ kind: 'arg', index: 2 })).toBe('a:2')
    expect(portKey({ kind: 'head' })).toBe('hd')
    expect(portKey({ kind: 'identity', index: 3 })).toBe('i:3')
  })

  it('derives exact ports and signatures for all three node kinds', () => {
    const atomSig = relSig([IOTA, relSig([])])
    const atom: DiagramNode = { kind: 'atom', region: 'r0', sig: atomSig }
    const ref: DiagramNode = { kind: 'ref', region: 'r0', defId: 'R', sig: atomSig }
    const identity: DiagramNode = {
      kind: 'identity',
      region: 'r0',
      sig: relSig([]),
      arity: 3,
    }

    expect(requiredPorts(atom).map(portKey)).toEqual(['hd', 'a:0', 'a:1'])
    expect(requiredPorts(ref).map(portKey)).toEqual(['a:0', 'a:1'])
    expect(requiredPorts(identity).map(portKey)).toEqual(['i:0', 'i:1', 'i:2'])
    expect(portSig(atom, { kind: 'head' })).toEqual(atomSig)
    expect(portSig(ref, { kind: 'arg', index: 1 })).toEqual(relSig([]))
    expect(portSig(identity, { kind: 'identity', index: 2 })).toEqual(relSig([]))
  })

  it('constructs a mixed atom/ref graph and accepts outer-scoped wires', () => {
    const sig = relSig([IOTA])
    const diagram = mkDiagram({
      root: 'r0',
      regions: {
        r0: { kind: 'sheet' },
        r1: { kind: 'cut', parent: 'r0' },
      },
      nodes: {
        atom: { kind: 'atom', region: 'r1', sig },
        ref: { kind: 'ref', region: 'r1', defId: 'P', sig },
        headPin: { kind: 'identity', region: 'r0', sig, arity: 1 },
        valuePin: { kind: 'identity', region: 'r0', sig: IOTA, arity: 1 },
      },
      wires: {
        relation: {
          sig,
          endpoints: [
            { node: 'atom', port: { kind: 'head' } },
            { node: 'headPin', port: { kind: 'identity', index: 0 } },
          ],
        },
        value: {
          sig: IOTA,
          endpoints: [
            { node: 'atom', port: { kind: 'arg', index: 0 } },
            { node: 'ref', port: { kind: 'arg', index: 0 } },
            { node: 'valuePin', port: { kind: 'identity', index: 0 } },
          ],
        },
      },
    })

    expect(Object.values(diagram.nodes).map((node) => node.kind).sort())
      .toEqual(['atom', 'identity', 'identity', 'ref'])
    expect(derivedScope(diagram, 'value')).toBe('r0')
  })

  it('does not alias unconstrained node ids with port keys', () => {
    expect(() => mkDiagram({
      root: 'r0',
      regions: { r0: { kind: 'sheet' } },
      nodes: {
        'n:a:0': { kind: 'ref', region: 'r0', defId: 'A', sig: relSig([IOTA]) },
        n: { kind: 'ref', region: 'r0', defId: 'B', sig: relSig([IOTA]) },
        firstPin: { kind: 'identity', region: 'r0', sig: IOTA, arity: 1 },
        secondPin: { kind: 'identity', region: 'r0', sig: IOTA, arity: 1 },
      },
      wires: {
        first: {
          sig: IOTA,
          endpoints: [
            { node: 'n:a:0', port: { kind: 'arg', index: 0 } },
            { node: 'firstPin', port: { kind: 'identity', index: 0 } },
          ],
        },
        second: {
          sig: IOTA,
          endpoints: [
            { node: 'n', port: { kind: 'arg', index: 0 } },
            { node: 'secondPin', port: { kind: 'identity', index: 0 } },
          ],
        },
      },
    })).not.toThrow()
  })
})
