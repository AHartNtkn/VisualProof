import { describe, expect, it } from 'vitest'
import type { DiagramNode, Wire } from '../../../src/kernel/diagram/diagram'
import { mkDiagram, validateRawDiagram } from '../../../src/kernel/diagram/diagram'
import {
  __isoCounters,
  diagramIso,
  sameDiagram,
} from '../../../src/kernel/diagram/canonical/iso'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'

/**
 * Disjoint rings of arity-2 identity nodes joined pairwise by wires.
 * rings([6]) asserts w1=…=w6; rings([3,3]) asserts two groups of three.
 * All nodes and wires are refinement-indistinguishable across the two.
 */
function rings(sizes: readonly number[]): ReturnType<typeof mkDiagram> {
  const nodes: Record<string, DiagramNode> = {}
  const wires: Record<string, Wire> = {}
  sizes.forEach((size, r) => {
    for (let i = 0; i < size; i++) {
      nodes[`id${r}_${i}`] = { kind: 'identity', region: 'root', sig: IOTA, arity: 2 }
    }
    for (let i = 0; i < size; i++) {
      wires[`w${r}_${i}`] = {
        sig: IOTA,
        endpoints: [
          { node: `id${r}_${i}`, port: { kind: 'identity', index: 1 } },
          { node: `id${r}_${(i + 1) % size}`, port: { kind: 'identity', index: 0 } },
        ],
      }
    }
  })
  return mkDiagram({ root: 'root', regions: { root: { kind: 'sheet' } }, nodes, wires })
}

/** rings() plus one hub identity wired to every ring node — connected variant. */
function hubbedRings(sizes: readonly number[]): ReturnType<typeof mkDiagram> {
  const total = sizes.reduce((s, x) => s + x, 0)
  const nodes: Record<string, DiagramNode> = {
    hub: { kind: 'identity', region: 'root', sig: IOTA, arity: total },
  }
  const wires: Record<string, Wire> = {}
  let spoke = 0
  sizes.forEach((size, r) => {
    for (let i = 0; i < size; i++) {
      nodes[`id${r}_${i}`] = { kind: 'identity', region: 'root', sig: IOTA, arity: 3 }
    }
    for (let i = 0; i < size; i++) {
      wires[`w${r}_${i}`] = {
        sig: IOTA,
        endpoints: [
          { node: `id${r}_${i}`, port: { kind: 'identity', index: 1 } },
          { node: `id${r}_${(i + 1) % size}`, port: { kind: 'identity', index: 0 } },
        ],
      }
      wires[`h${r}_${i}`] = {
        sig: IOTA,
        endpoints: [
          { node: `id${r}_${i}`, port: { kind: 'identity', index: 2 } },
          { node: 'hub', port: { kind: 'identity', index: spoke++ } },
        ],
      }
    }
  })
  return mkDiagram({ root: 'root', regions: { root: { kind: 'sheet' } }, nodes, wires })
}

const rel1 = relSig([IOTA])

describe('pairwise diagram isomorphism', () => {
  it('SOUNDNESS: one six-ring is not two three-rings (refinement-blind pair)', () => {
    expect(sameDiagram(rings([6]), rings([3, 3]))).toBe(false)
    expect(sameDiagram(rings([3, 3]), rings([6]))).toBe(false)
  })

  it('SOUNDNESS: hub-connected variant is also distinguished', () => {
    expect(sameDiagram(hubbedRings([6]), hubbedRings([3, 3]))).toBe(false)
  })

  it('finds and verifies an iso between equal symmetric structures', () => {
    const iso = diagramIso(rings([3, 3]), rings([3, 3]))
    expect(iso).not.toBeNull()
    expect(iso!.nodes.size).toBe(6)
    expect(iso!.wires.size).toBe(6)
  })

  it('DORMANCY: orbit-clean symmetric diagrams need zero failed candidates', () => {
    __isoCounters.failedCandidates = 0
    expect(diagramIso(rings([3, 3]), rings([3, 3]))).not.toBeNull()
    expect(diagramIso(rings([5]), rings([5]))).not.toBeNull()
    expect(__isoCounters.failedCandidates).toBe(0)
  })

  it('respects pinned boundary order, including refusing a swap', () => {
    // x and y are boundary-exposed (their boundary entry is their second
    // end); mkDiagram alone rejects wires with only one stored endpoint, so
    // this fixture is built via validateRawDiagram with an explicit
    // boundary, mirroring boundary.ts mkDiagramWithBoundary.
    const d = validateRawDiagram({
      root: 'root',
      regions: { root: { kind: 'sheet' } },
      nodes: {
        a: { kind: 'atom', region: 'root', sig: relSig([IOTA, IOTA]) },
        pin: { kind: 'identity', region: 'root', sig: relSig([IOTA, IOTA]), arity: 1 },
      },
      wires: {
        head: { sig: relSig([IOTA, IOTA]), endpoints: [
          { node: 'a', port: { kind: 'head' } },
          { node: 'pin', port: { kind: 'identity', index: 0 } },
        ] },
        x: { sig: IOTA, endpoints: [{ node: 'a', port: { kind: 'arg', index: 0 } }] },
        y: { sig: IOTA, endpoints: [{ node: 'a', port: { kind: 'arg', index: 1 } }] },
      },
    }, ['x', 'y'])
    expect(sameDiagram(d, d, ['x', 'y'], ['x', 'y'])).toBe(true)
    expect(sameDiagram(d, d, ['x', 'y'], ['y', 'x'])).toBe(false)
    const iso = diagramIso(d, d, ['x', 'y'], ['x', 'y'])
    expect(iso!.wires.get('x')).toBe('x')
    expect(iso!.wires.get('y')).toBe('y')
  })

  it('is id-invariant: a wholesale renaming is recovered', () => {
    const make = (p: string) => mkDiagram({
      root: `${p}root`,
      regions: {
        [`${p}root`]: { kind: 'sheet' },
        [`${p}cut`]: { kind: 'cut', parent: `${p}root` },
      },
      nodes: {
        [`${p}atom`]: { kind: 'atom', region: `${p}cut`, sig: rel1 },
        [`${p}ref`]: { kind: 'ref', region: `${p}root`, defId: 'P', sig: rel1 },
        [`${p}hpin`]: { kind: 'identity', region: `${p}root`, sig: rel1, arity: 1 },
      },
      wires: {
        [`${p}head`]: { sig: rel1, endpoints: [
          { node: `${p}atom`, port: { kind: 'head' } },
          { node: `${p}hpin`, port: { kind: 'identity', index: 0 } },
        ] },
        [`${p}val`]: { sig: IOTA, endpoints: [
          { node: `${p}ref`, port: { kind: 'arg', index: 0 } },
          { node: `${p}atom`, port: { kind: 'arg', index: 0 } },
        ] },
      },
    })
    const iso = diagramIso(make('L'), make('R'))
    expect(iso).not.toBeNull()
    expect(iso!.regions.get('Lroot')).toBe('Rroot')
    expect(iso!.regions.get('Lcut')).toBe('Rcut')
    expect(iso!.nodes.get('Latom')).toBe('Ratom')
    expect(iso!.wires.get('Lval')).toBe('Rval')
  })

  it('rejects on plain census differences immediately', () => {
    expect(sameDiagram(rings([3]), rings([4]))).toBe(false)
    expect(sameDiagram(rings([3]), rings([3, 3]))).toBe(false)
  })

  it('rejects when pin arities differ', () => {
    const a = rings([3])
    expect(sameDiagram(a, a, ['w0_0'], [])).toBe(false)
  })
})
