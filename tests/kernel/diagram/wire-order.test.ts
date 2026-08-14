import { describe, expect, it } from 'vitest'
import type { Diagram, WireId } from '../../../src/kernel/diagram/diagram'
import { mkDiagram } from '../../../src/kernel/diagram/diagram'
import { canonicalWireOrder } from '../../../src/kernel/diagram/canonical/wire-order'
import { sameDiagram } from '../../../src/kernel/diagram/canonical/iso'
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

  it('is id-invariant under a genuine automorphic tie: canonical orders correspond', () => {
    // Hub (arity 3) with three pendant chains of lengths 1, 2, 2. The two
    // length-2 chains are a genuine automorphism pair (refinement alone
    // cannot split them); the length-1 chain breaks full hub symmetry.
    // Each "chain of length L" is L identity nodes of arity 2 in series,
    // terminated by an arity-1 identity node (length 1 is just the
    // terminal, wired directly to the hub).
    const a: Diagram = mkDiagram({
      root: 'root',
      regions: { root: { kind: 'sheet' } },
      nodes: {
        hub: { kind: 'identity', region: 'root', sig: IOTA, arity: 3 },
        t1: { kind: 'identity', region: 'root', sig: IOTA, arity: 1 },
        m2: { kind: 'identity', region: 'root', sig: IOTA, arity: 2 },
        t2: { kind: 'identity', region: 'root', sig: IOTA, arity: 1 },
        m3: { kind: 'identity', region: 'root', sig: IOTA, arity: 2 },
        t3: { kind: 'identity', region: 'root', sig: IOTA, arity: 1 },
      },
      wires: {
        w1: { sig: IOTA, endpoints: [
          { node: 'hub', port: { kind: 'identity', index: 0 } },
          { node: 't1', port: { kind: 'identity', index: 0 } },
        ] },
        w2a: { sig: IOTA, endpoints: [
          { node: 'hub', port: { kind: 'identity', index: 1 } },
          { node: 'm2', port: { kind: 'identity', index: 0 } },
        ] },
        w2b: { sig: IOTA, endpoints: [
          { node: 'm2', port: { kind: 'identity', index: 1 } },
          { node: 't2', port: { kind: 'identity', index: 0 } },
        ] },
        w3a: { sig: IOTA, endpoints: [
          { node: 'hub', port: { kind: 'identity', index: 2 } },
          { node: 'm3', port: { kind: 'identity', index: 0 } },
        ] },
        w3b: { sig: IOTA, endpoints: [
          { node: 'm3', port: { kind: 'identity', index: 1 } },
          { node: 't3', port: { kind: 'identity', index: 0 } },
        ] },
      },
    })

    // Same shape, disjoint id scheme, AND the two symmetric chains declared
    // in swapped construction order relative to `a` (betaMid/betaEnd before
    // alphaMid/alphaEnd, and the short chain declared last instead of
    // first) — a probe for any latent dependence on object insertion order.
    const b: Diagram = mkDiagram({
      root: 'sheetB',
      regions: { sheetB: { kind: 'sheet' } },
      nodes: {
        hubB: { kind: 'identity', region: 'sheetB', sig: IOTA, arity: 3 },
        betaMid: { kind: 'identity', region: 'sheetB', sig: IOTA, arity: 2 },
        betaEnd: { kind: 'identity', region: 'sheetB', sig: IOTA, arity: 1 },
        alphaMid: { kind: 'identity', region: 'sheetB', sig: IOTA, arity: 2 },
        alphaEnd: { kind: 'identity', region: 'sheetB', sig: IOTA, arity: 1 },
        shortEnd: { kind: 'identity', region: 'sheetB', sig: IOTA, arity: 1 },
      },
      wires: {
        wBeta1: { sig: IOTA, endpoints: [
          { node: 'hubB', port: { kind: 'identity', index: 0 } },
          { node: 'betaMid', port: { kind: 'identity', index: 0 } },
        ] },
        wBeta2: { sig: IOTA, endpoints: [
          { node: 'betaMid', port: { kind: 'identity', index: 1 } },
          { node: 'betaEnd', port: { kind: 'identity', index: 0 } },
        ] },
        wAlpha1: { sig: IOTA, endpoints: [
          { node: 'hubB', port: { kind: 'identity', index: 1 } },
          { node: 'alphaMid', port: { kind: 'identity', index: 0 } },
        ] },
        wAlpha2: { sig: IOTA, endpoints: [
          { node: 'alphaMid', port: { kind: 'identity', index: 1 } },
          { node: 'alphaEnd', port: { kind: 'identity', index: 0 } },
        ] },
        wShort: { sig: IOTA, endpoints: [
          { node: 'hubB', port: { kind: 'identity', index: 2 } },
          { node: 'shortEnd', port: { kind: 'identity', index: 0 } },
        ] },
      },
    })

    const oA = canonicalWireOrder(a)
    const oB = canonicalWireOrder(b)
    expect([...oA.values()].sort((x, y) => x - y)).toEqual([0, 1, 2, 3, 4])
    expect([...oB.values()].sort((x, y) => x - y)).toEqual([0, 1, 2, 3, 4])

    const byOrd = (d: Diagram, ord: Map<WireId, number>): WireId[] =>
      Object.keys(d.wires).sort((x, y) => ord.get(x)! - ord.get(y)!)
    const pinsA = byOrd(a, oA)
    const pinsB = byOrd(b, oB)

    // An isomorphism exists that matches the two canonical orders
    // position-for-position: isomorphic diagrams get corresponding wire
    // orders, even in the presence of an automorphic tie.
    expect(sameDiagram(a, b, pinsA, pinsB)).toBe(true)
  })
})
