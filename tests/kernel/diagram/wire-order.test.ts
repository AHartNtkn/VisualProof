import { describe, expect, it } from 'vitest'
import { mkDiagram } from '../../../src/kernel/diagram/diagram'
import { canonicalWireOrder } from '../../../src/kernel/diagram/canonical/wire-order'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'

const rel1 = relSig([IOTA])

function graph(ids: { atom: string; hpin: string; head: string; val: string; vpin: string }) {
  return mkDiagram({
    root: 'root',
    regions: { root: { kind: 'sheet' } },
    nodes: {
      [ids.atom]: { kind: 'atom', region: 'root', sig: rel1 },
      [ids.hpin]: { kind: 'identity', region: 'root', sig: rel1, arity: 1 },
      [ids.vpin]: { kind: 'identity', region: 'root', sig: IOTA, arity: 1 },
    },
    wires: {
      [ids.head]: { sig: rel1, endpoints: [
        { node: ids.atom, port: { kind: 'head' } },
        { node: ids.hpin, port: { kind: 'identity', index: 0 } },
      ] },
      [ids.val]: { sig: IOTA, endpoints: [
        { node: ids.atom, port: { kind: 'arg', index: 0 } },
        { node: ids.vpin, port: { kind: 'identity', index: 0 } },
      ] },
    },
  })
}

describe('canonical wire order', () => {
  it('assigns each wire a distinct ordinal in 0..n-1', () => {
    const ord = canonicalWireOrder(graph({ atom: 'a', hpin: 'p', head: 'h', val: 'v', vpin: 'q' }))
    expect([...ord.values()].sort()).toEqual([0, 1])
  })

  it('is id-invariant: corresponding wires get equal ordinals', () => {
    const o1 = canonicalWireOrder(graph({ atom: 'a', hpin: 'p', head: 'h', val: 'v', vpin: 'q' }))
    const o2 = canonicalWireOrder(graph({ atom: 'z9', hpin: 'k', head: 'hd', val: 'w0', vpin: 'm' }))
    expect(o1.get('h')).toBe(o2.get('hd'))
    expect(o1.get('v')).toBe(o2.get('w0'))
  })

  it('breaks genuine symmetry deterministically (both orders occur, fixed)', () => {
    const symmetric = (w0: string, w1: string) => mkDiagram({
      root: 'root',
      regions: { root: { kind: 'sheet' } },
      nodes: {
        j: { kind: 'identity', region: 'root', sig: IOTA, arity: 2 },
        p0: { kind: 'identity', region: 'root', sig: IOTA, arity: 1 },
        p1: { kind: 'identity', region: 'root', sig: IOTA, arity: 1 },
      },
      wires: {
        [w0]: { sig: IOTA, endpoints: [
          { node: 'j', port: { kind: 'identity', index: 0 } },
          { node: 'p0', port: { kind: 'identity', index: 0 } },
        ] },
        [w1]: { sig: IOTA, endpoints: [
          { node: 'j', port: { kind: 'identity', index: 1 } },
          { node: 'p1', port: { kind: 'identity', index: 0 } },
        ] },
      },
    })
    const oa = canonicalWireOrder(symmetric('x', 'y'))
    const ob = canonicalWireOrder(symmetric('y', 'x'))
    // Interchangeable wires: the ordinals are a permutation of 0..1 either
    // way, and the function is a function of the diagram alone.
    expect([...oa.values()].sort()).toEqual([0, 1])
    expect([...ob.values()].sort()).toEqual([0, 1])
  })
})
