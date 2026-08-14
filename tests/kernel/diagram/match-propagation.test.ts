import { describe, expect, it } from 'vitest'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { mkDiagram } from '../../../src/kernel/diagram/diagram'
import { __initCandidates, __propagate, __makePropagationContext } from '../../../src/kernel/diagram/subgraph/match'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'

const rel2 = relSig([IOTA, IOTA])

/** Host: chain ref d0 -(w0)- ref d1 -(w1)- ref d2, ends pinned. Distinct defIds. */
function chainHost() {
  return mkDiagram({
    root: 'root',
    regions: { root: { kind: 'sheet' } },
    nodes: {
      r0: { kind: 'ref', region: 'root', defId: 'd0', sig: rel2 },
      r1: { kind: 'ref', region: 'root', defId: 'd1', sig: rel2 },
      r2: { kind: 'ref', region: 'root', defId: 'd2', sig: rel2 },
      pL: { kind: 'identity', region: 'root', sig: IOTA, arity: 1 },
      pR: { kind: 'identity', region: 'root', sig: IOTA, arity: 1 },
    },
    wires: {
      end0: { sig: IOTA, endpoints: [
        { node: 'r0', port: { kind: 'arg', index: 0 } },
        { node: 'pL', port: { kind: 'identity', index: 0 } },
      ] },
      w0: { sig: IOTA, endpoints: [
        { node: 'r0', port: { kind: 'arg', index: 1 } },
        { node: 'r1', port: { kind: 'arg', index: 0 } },
      ] },
      w1: { sig: IOTA, endpoints: [
        { node: 'r1', port: { kind: 'arg', index: 1 } },
        { node: 'r2', port: { kind: 'arg', index: 0 } },
      ] },
      end1: { sig: IOTA, endpoints: [
        { node: 'r2', port: { kind: 'arg', index: 1 } },
        { node: 'pR', port: { kind: 'identity', index: 0 } },
      ] },
    },
  })
}

/** Pattern: single ref d1 with both args boundary-exposed. */
function d1Pattern() {
  return mkDiagramWithBoundary(
    {
      root: 'proot',
      regions: { proot: { kind: 'sheet' } },
      nodes: { n: { kind: 'ref', region: 'proot', defId: 'd1', sig: rel2 } },
      wires: {
        a: { sig: IOTA, endpoints: [{ node: 'n', port: { kind: 'arg', index: 0 } }] },
        b: { sig: IOTA, endpoints: [{ node: 'n', port: { kind: 'arg', index: 1 } }] },
      },
    },
    ['a', 'b'],
  )
}

describe('matcher candidate propagation', () => {
  it('content filtering pins a distinct ref to its unique host image', () => {
    const host = chainHost()
    const pattern = d1Pattern()
    const ctx = __makePropagationContext(host, pattern, {})
    const cands = __initCandidates(ctx)
    expect(cands).not.toBeNull()
    expect([...cands!.node.get('n')!]).toEqual(['r1'])
  })

  it('positional-port propagation forces the boundary wire images', () => {
    const host = chainHost()
    const pattern = d1Pattern()
    const ctx = __makePropagationContext(host, pattern, {})
    const cands = __initCandidates(ctx)!
    const ok = __propagate(ctx, cands)
    expect(ok).toBe(true)
    expect([...cands.wire.get('a')!]).toEqual(['w0'])
    expect([...cands.wire.get('b')!]).toEqual(['w1'])
  })

  it('a contradictory seed empties a candidate set', () => {
    const host = chainHost()
    const pattern = d1Pattern()
    // Seed boundary position 0 (wire a) to end1 — but a must be r1's arg0
    // wire, which is w0. Init keeps the seed; propagation must fail.
    const ctx = __makePropagationContext(host, pattern, { attachments: ['end1', 'w1'] })
    const cands = __initCandidates(ctx)!
    expect(__propagate(ctx, cands)).toBe(false)
  })

  it('nested-cut fingerprints restrict cut candidates to census-equal cuts', () => {
    const host = mkDiagram({
      root: 'root',
      regions: {
        root: { kind: 'sheet' },
        empty: { kind: 'cut', parent: 'root' },
        full: { kind: 'cut', parent: 'root' },
      },
      nodes: { j: { kind: 'identity', region: 'full', sig: IOTA, arity: 0 } },
      wires: {},
    })
    const pattern = mkDiagramWithBoundary(
      {
        root: 'proot',
        regions: { proot: { kind: 'sheet' }, pcut: { kind: 'cut', parent: 'proot' } },
        nodes: {},
        wires: {},
      },
      [],
    )
    const ctx = __makePropagationContext(host, pattern, {})
    const cands = __initCandidates(ctx)!
    expect([...cands.region.get('pcut')!]).toEqual(['empty'])
  })
})
