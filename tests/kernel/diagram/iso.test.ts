import { describe, expect, it } from 'vitest'
import type { DiagramNode, Wire } from '../../../src/kernel/diagram/diagram'
import { mkDiagram, validateRawDiagram } from '../../../src/kernel/diagram/diagram'
import type { DiagramIso } from '../../../src/kernel/diagram/canonical/iso'
import {
  __isoCounters,
  __verifyIso,
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

/**
 * DIRECT NEGATIVE TESTS FOR __verifyIso.
 *
 * On genuine engine inputs every rejection branch of `__verifyIso` is
 * unreachable through `diagramIso`/`sameDiagram`: a discrete census-matched
 * coloring provably transports structure, so the search never hands
 * `__verifyIso` a witness that fails its own check. Each test below builds a
 * valid diagram pair and a DELIBERATELY WRONG `DiagramIso` witness, then
 * calls `__verifyIso` directly to exercise one specific rejection branch —
 * the only way to reach it at all.
 */
describe('__verifyIso direct branch tests', () => {
  it('rejects a region kind mismatch (sheet mapped to a cut)', () => {
    const a = mkDiagram({
      root: 'root',
      regions: { root: { kind: 'sheet' }, c: { kind: 'cut', parent: 'root' } },
    })
    const b = mkDiagram({
      root: 'root',
      regions: { root: { kind: 'sheet' }, c: { kind: 'cut', parent: 'root' } },
    })
    const iso: DiagramIso = {
      regions: new Map([['root', 'c'], ['c', 'root']]),
      nodes: new Map(),
      wires: new Map(),
    }
    const reason = __verifyIso(a, b, [], [], iso)
    expect(reason).toContain("kind 'sheet' does not match 'c' kind 'cut'")
  })

  it('rejects a region parent transport failure', () => {
    const a = mkDiagram({
      root: 'root',
      regions: {
        root: { kind: 'sheet' },
        c1: { kind: 'cut', parent: 'root' },
        c2: { kind: 'cut', parent: 'c1' },
      },
    })
    const b = mkDiagram({
      root: 'root',
      regions: {
        root: { kind: 'sheet' },
        d1: { kind: 'cut', parent: 'root' },
        d2: { kind: 'cut', parent: 'root' },
      },
    })
    const iso: DiagramIso = {
      regions: new Map([['root', 'root'], ['c1', 'd1'], ['c2', 'd2']]),
      nodes: new Map(),
      wires: new Map(),
    }
    const reason = __verifyIso(a, b, [], [], iso)
    expect(reason).toContain("region 'c2' parent does not transport to region 'd2' parent")
  })

  it('rejects an atom sig mismatch', () => {
    const nested = relSig([])
    const make = (argSig: typeof IOTA | typeof nested) => mkDiagram({
      root: 'root',
      regions: { root: { kind: 'sheet' } },
      nodes: {
        atom: { kind: 'atom', region: 'root', sig: relSig([argSig]) },
        headPin: { kind: 'identity', region: 'root', sig: relSig([argSig]), arity: 1 },
        argPin: { kind: 'identity', region: 'root', sig: argSig, arity: 1 },
      },
      wires: {
        head: { sig: relSig([argSig]), endpoints: [
          { node: 'atom', port: { kind: 'head' } },
          { node: 'headPin', port: { kind: 'identity', index: 0 } },
        ] },
        arg: { sig: argSig, endpoints: [
          { node: 'atom', port: { kind: 'arg', index: 0 } },
          { node: 'argPin', port: { kind: 'identity', index: 0 } },
        ] },
      },
    })
    const a = make(IOTA)
    const b = make(nested)
    const iso: DiagramIso = {
      regions: new Map([['root', 'root']]),
      nodes: new Map([['atom', 'atom'], ['headPin', 'headPin'], ['argPin', 'argPin']]),
      wires: new Map([['head', 'head'], ['arg', 'arg']]),
    }
    const reason = __verifyIso(a, b, [], [], iso)
    expect(reason).toContain("atom 'atom' sig does not match 'atom' sig")
  })

  it('rejects a ref defId mismatch', () => {
    const make = (defId: string) => mkDiagram({
      root: 'root',
      regions: { root: { kind: 'sheet' } },
      nodes: { ref: { kind: 'ref', region: 'root', defId, sig: relSig([]) } },
    })
    const a = make('P')
    const b = make('Q')
    const iso: DiagramIso = {
      regions: new Map([['root', 'root']]),
      nodes: new Map([['ref', 'ref']]),
      wires: new Map(),
    }
    const reason = __verifyIso(a, b, [], [], iso)
    expect(reason).toContain("ref 'ref' defId 'P' does not match 'ref' defId 'Q'")
  })

  it('rejects an identity arity mismatch', () => {
    const a = mkDiagram({
      root: 'root',
      regions: { root: { kind: 'sheet' } },
      nodes: {
        idA: { kind: 'identity', region: 'root', sig: IOTA, arity: 1 },
        helperA: { kind: 'identity', region: 'root', sig: IOTA, arity: 1 },
      },
      wires: {
        wA: { sig: IOTA, endpoints: [
          { node: 'idA', port: { kind: 'identity', index: 0 } },
          { node: 'helperA', port: { kind: 'identity', index: 0 } },
        ] },
      },
    })
    const b = mkDiagram({
      root: 'root',
      regions: { root: { kind: 'sheet' } },
      nodes: {
        idB: { kind: 'identity', region: 'root', sig: IOTA, arity: 2 },
        helperB: { kind: 'identity', region: 'root', sig: IOTA, arity: 0 },
      },
      wires: {
        wB: { sig: IOTA, endpoints: [
          { node: 'idB', port: { kind: 'identity', index: 0 } },
          { node: 'idB', port: { kind: 'identity', index: 1 } },
        ] },
      },
    })
    const iso: DiagramIso = {
      regions: new Map([['root', 'root']]),
      nodes: new Map([['idA', 'idB'], ['helperA', 'helperB']]),
      wires: new Map([['wA', 'wB']]),
    }
    const reason = __verifyIso(a, b, [], [], iso)
    expect(reason).toContain("identity 'idA' arity 1 does not match 'idB' arity 2")
  })

  it('rejects a node region transport failure', () => {
    const regions = { root: { kind: 'sheet' as const }, c: { kind: 'cut' as const, parent: 'root' } }
    const a = mkDiagram({
      root: 'root',
      regions,
      nodes: { nA: { kind: 'identity', region: 'root', sig: IOTA, arity: 0 } },
    })
    const b = mkDiagram({
      root: 'root',
      regions,
      nodes: { nB: { kind: 'identity', region: 'c', sig: IOTA, arity: 0 } },
    })
    const iso: DiagramIso = {
      regions: new Map([['root', 'root'], ['c', 'c']]),
      nodes: new Map([['nA', 'nB']]),
      wires: new Map(),
    }
    const reason = __verifyIso(a, b, [], [], iso)
    expect(reason).toContain("node 'nA' region does not transport to node 'nB' region")
  })

  it('rejects a wire sig mismatch', () => {
    const nested = relSig([])
    const make = (prefix: string) => mkDiagram({
      root: 'root',
      regions: { root: { kind: 'sheet' } },
      nodes: {
        [`${prefix}1`]: { kind: 'identity', region: 'root', sig: IOTA, arity: 1 },
        [`${prefix}2`]: { kind: 'identity', region: 'root', sig: IOTA, arity: 1 },
        [`${prefix}3`]: { kind: 'identity', region: 'root', sig: nested, arity: 1 },
        [`${prefix}4`]: { kind: 'identity', region: 'root', sig: nested, arity: 1 },
      },
      wires: {
        [`w${prefix}`]: { sig: IOTA, endpoints: [
          { node: `${prefix}1`, port: { kind: 'identity', index: 0 } },
          { node: `${prefix}2`, port: { kind: 'identity', index: 0 } },
        ] },
        [`w${prefix}2`]: { sig: nested, endpoints: [
          { node: `${prefix}3`, port: { kind: 'identity', index: 0 } },
          { node: `${prefix}4`, port: { kind: 'identity', index: 0 } },
        ] },
      },
    })
    const a = make('a')
    const b = make('b')
    const iso: DiagramIso = {
      regions: new Map([['root', 'root']]),
      nodes: new Map([['a1', 'b1'], ['a2', 'b2'], ['a3', 'b3'], ['a4', 'b4']]),
      wires: new Map([['wa', 'wb2'], ['wa2', 'wb']]),
    }
    const reason = __verifyIso(a, b, [], [], iso)
    expect(reason).toContain("wire 'wa' sig does not match 'wb2' sig")
  })

  it('rejects a wire endpoint-multiset transport failure (swapped images on an asymmetric pair)', () => {
    const make = (prefix: string) => mkDiagram({
      root: 'root',
      regions: { root: { kind: 'sheet' } },
      nodes: {
        [`${prefix}p`]: { kind: 'identity', region: 'root', sig: IOTA, arity: 2 },
        [`${prefix}h1`]: { kind: 'identity', region: 'root', sig: IOTA, arity: 1 },
        [`${prefix}h2`]: { kind: 'identity', region: 'root', sig: IOTA, arity: 1 },
      },
      wires: {
        [`${prefix}w1`]: { sig: IOTA, endpoints: [
          { node: `${prefix}p`, port: { kind: 'identity', index: 0 } },
          { node: `${prefix}h1`, port: { kind: 'identity', index: 0 } },
        ] },
        [`${prefix}w2`]: { sig: IOTA, endpoints: [
          { node: `${prefix}p`, port: { kind: 'identity', index: 1 } },
          { node: `${prefix}h2`, port: { kind: 'identity', index: 0 } },
        ] },
      },
    })
    const a = make('a')
    const b = make('b')
    const iso: DiagramIso = {
      regions: new Map([['root', 'root']]),
      nodes: new Map([['ap', 'bp'], ['ah1', 'bh1'], ['ah2', 'bh2']]),
      wires: new Map([['aw1', 'bw2'], ['aw2', 'bw1']]),
    }
    const reason = __verifyIso(a, b, [], [], iso)
    expect(reason).toContain("wire 'aw1' endpoints do not transport to wire 'bw2' endpoints")
  })

  it('rejects a pin position transport failure', () => {
    const d = validateRawDiagram({
      root: 'root',
      regions: { root: { kind: 'sheet' } },
      nodes: {
        atom: { kind: 'atom', region: 'root', sig: relSig([IOTA, IOTA]) },
        pin: { kind: 'identity', region: 'root', sig: relSig([IOTA, IOTA]), arity: 1 },
      },
      wires: {
        head: { sig: relSig([IOTA, IOTA]), endpoints: [
          { node: 'atom', port: { kind: 'head' } },
          { node: 'pin', port: { kind: 'identity', index: 0 } },
        ] },
        x: { sig: IOTA, endpoints: [{ node: 'atom', port: { kind: 'arg', index: 0 } }] },
        y: { sig: IOTA, endpoints: [{ node: 'atom', port: { kind: 'arg', index: 1 } }] },
      },
    }, ['x', 'y'])
    const iso: DiagramIso = {
      regions: new Map([['root', 'root']]),
      nodes: new Map([['atom', 'atom'], ['pin', 'pin']]),
      wires: new Map([['head', 'head'], ['x', 'x'], ['y', 'y']]),
    }
    const reason = __verifyIso(d, d, ['x', 'y'], ['y', 'x'], iso)
    expect(reason).toContain("pin 0: wire 'x' maps to 'x', expected 'y'")
  })

  it('rejects a non-bijective map with a missing entry', () => {
    const a = mkDiagram({
      root: 'root',
      regions: { root: { kind: 'sheet' }, c: { kind: 'cut', parent: 'root' } },
    })
    const b = mkDiagram({
      root: 'root',
      regions: { root: { kind: 'sheet' }, c: { kind: 'cut', parent: 'root' } },
    })
    const iso: DiagramIso = {
      regions: new Map([['root', 'root']]),
      nodes: new Map(),
      wires: new Map(),
    }
    const reason = __verifyIso(a, b, [], [], iso)
    expect(reason).toContain('regions map has 1 entries; expected 2')
  })

  it('rejects a non-bijective two-to-one map', () => {
    const a = mkDiagram({
      root: 'root',
      regions: { root: { kind: 'sheet' }, c: { kind: 'cut', parent: 'root' } },
    })
    const b = mkDiagram({
      root: 'root',
      regions: { root: { kind: 'sheet' }, c: { kind: 'cut', parent: 'root' } },
    })
    const iso: DiagramIso = {
      regions: new Map([['root', 'root'], ['c', 'root']]),
      nodes: new Map(),
      wires: new Map(),
    }
    const reason = __verifyIso(a, b, [], [], iso)
    expect(reason).toContain("regions map is not injective: 'root' has more than one preimage")
  })

  it('rejects a checkBijection map with a key outside its domain', () => {
    const a = mkDiagram({
      root: 'root',
      regions: { root: { kind: 'sheet' }, c: { kind: 'cut', parent: 'root' } },
    })
    const b = mkDiagram({
      root: 'root',
      regions: { root: { kind: 'sheet' }, c: { kind: 'cut', parent: 'root' } },
    })
    const iso: DiagramIso = {
      regions: new Map([['root', 'root'], ['extra', 'c']]),
      nodes: new Map(),
      wires: new Map(),
    }
    const reason = __verifyIso(a, b, [], [], iso)
    expect(reason).toContain("regions map has unexpected key 'extra'")
  })

  it('rejects a checkBijection map with a value outside its codomain', () => {
    const a = mkDiagram({
      root: 'root',
      regions: { root: { kind: 'sheet' }, c: { kind: 'cut', parent: 'root' } },
    })
    const b = mkDiagram({
      root: 'root',
      regions: { root: { kind: 'sheet' }, c: { kind: 'cut', parent: 'root' } },
    })
    const iso: DiagramIso = {
      regions: new Map([['root', 'bogus'], ['c', 'root']]),
      nodes: new Map(),
      wires: new Map(),
    }
    const reason = __verifyIso(a, b, [], [], iso)
    expect(reason).toContain("regions map targets unknown 'bogus'")
  })

  it('rejects a checkBijection map that is injective but not onto (smaller domain)', () => {
    const a = mkDiagram({
      root: 'root',
      regions: { root: { kind: 'sheet' } },
    })
    const b = mkDiagram({
      root: 'root',
      regions: { root: { kind: 'sheet' }, c: { kind: 'cut', parent: 'root' } },
    })
    const iso: DiagramIso = {
      regions: new Map([['root', 'root']]),
      nodes: new Map(),
      wires: new Map(),
    }
    const reason = __verifyIso(a, b, [], [], iso)
    expect(reason).toContain('regions map is not onto its codomain')
  })

  it('rejects a node kind mismatch (atom mapped to identity)', () => {
    const a = mkDiagram({
      root: 'root',
      regions: { root: { kind: 'sheet' } },
      nodes: {
        atomA: { kind: 'atom', region: 'root', sig: relSig([]) },
        pinA: { kind: 'identity', region: 'root', sig: relSig([]), arity: 1 },
      },
      wires: {
        headA: { sig: relSig([]), endpoints: [
          { node: 'atomA', port: { kind: 'head' } },
          { node: 'pinA', port: { kind: 'identity', index: 0 } },
        ] },
      },
    })
    const b = mkDiagram({
      root: 'root',
      regions: { root: { kind: 'sheet' } },
      nodes: {
        idB: { kind: 'identity', region: 'root', sig: relSig([]), arity: 1 },
        extraB: { kind: 'identity', region: 'root', sig: relSig([]), arity: 1 },
      },
      wires: {
        wB: { sig: relSig([]), endpoints: [
          { node: 'idB', port: { kind: 'identity', index: 0 } },
          { node: 'extraB', port: { kind: 'identity', index: 0 } },
        ] },
      },
    })
    const iso: DiagramIso = {
      regions: new Map([['root', 'root']]),
      nodes: new Map([['atomA', 'idB'], ['pinA', 'extraB']]),
      wires: new Map([['headA', 'wB']]),
    }
    const reason = __verifyIso(a, b, [], [], iso)
    expect(reason).toContain("node 'atomA' kind 'atom' does not match 'idB' kind 'identity'")
  })

  it('rejects a ref sig mismatch with an equal defId', () => {
    const nested = relSig([])
    const make = (argSig: typeof IOTA | typeof nested) => mkDiagram({
      root: 'root',
      regions: { root: { kind: 'sheet' } },
      nodes: {
        ref: { kind: 'ref', region: 'root', defId: 'P', sig: relSig([argSig]) },
        argPin: { kind: 'identity', region: 'root', sig: argSig, arity: 1 },
      },
      wires: {
        arg: { sig: argSig, endpoints: [
          { node: 'ref', port: { kind: 'arg', index: 0 } },
          { node: 'argPin', port: { kind: 'identity', index: 0 } },
        ] },
      },
    })
    const a = make(IOTA)
    const b = make(nested)
    const iso: DiagramIso = {
      regions: new Map([['root', 'root']]),
      nodes: new Map([['ref', 'ref'], ['argPin', 'argPin']]),
      wires: new Map([['arg', 'arg']]),
    }
    const reason = __verifyIso(a, b, [], [], iso)
    expect(reason).toContain("ref 'ref' sig does not match 'ref' sig")
  })

  it('rejects an identity sig mismatch with an equal arity', () => {
    const a = mkDiagram({
      root: 'root',
      regions: { root: { kind: 'sheet' } },
      nodes: {
        idA: { kind: 'identity', region: 'root', sig: IOTA, arity: 1 },
        helperA: { kind: 'identity', region: 'root', sig: IOTA, arity: 1 },
      },
      wires: {
        wA: { sig: IOTA, endpoints: [
          { node: 'idA', port: { kind: 'identity', index: 0 } },
          { node: 'helperA', port: { kind: 'identity', index: 0 } },
        ] },
      },
    })
    const nested = relSig([])
    const b = mkDiagram({
      root: 'root',
      regions: { root: { kind: 'sheet' } },
      nodes: {
        idB: { kind: 'identity', region: 'root', sig: nested, arity: 1 },
        helperB: { kind: 'identity', region: 'root', sig: nested, arity: 1 },
      },
      wires: {
        wB: { sig: nested, endpoints: [
          { node: 'idB', port: { kind: 'identity', index: 0 } },
          { node: 'helperB', port: { kind: 'identity', index: 0 } },
        ] },
      },
    })
    const iso: DiagramIso = {
      regions: new Map([['root', 'root']]),
      nodes: new Map([['idA', 'idB'], ['helperA', 'helperB']]),
      wires: new Map([['wA', 'wB']]),
    }
    const reason = __verifyIso(a, b, [], [], iso)
    expect(reason).toContain("identity 'idA' sig does not match 'idB' sig")
  })
})
