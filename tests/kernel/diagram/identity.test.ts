import { describe, expect, it } from 'vitest'
import {
  mkDiagram,
  type DiagramNode,
  type DiagramParts,
  type Endpoint,
} from '../../../src/kernel/diagram/diagram'
import { exploreForm } from '../../../src/kernel/diagram/canonical/explore'
import { diagramFromJson, diagramToJson } from '../../../src/kernel/diagram/json'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'

const sheet = { r0: { kind: 'sheet' as const } }

// NEEDS-ADJUDICATION: most of this file was written against
// mkDiagramNormalized and its wireImage — the eager identity normalizer,
// which is deleted. The fixtures below are converted to the new
// representation (every wire end is a node, so each free end carries a pin),
// but the claims about identities disappearing at construction time no
// longer hold: identity nodes persist until an identification or
// presentation step changes them. Those tests now fail, deliberately.

/** A pin: the node holding a wire's free end, and its quantifier, at `region`. */
function pin(region: string): DiagramNode {
  return { kind: 'identity', region, sig: IOTA, arity: 1 }
}

function pinEnd(node: string): Endpoint {
  return { node, port: { kind: 'identity', index: 0 } }
}

function identityParts(
  wireIds: readonly string[],
  opts: {
    readonly arity?: number
    readonly region?: string
    readonly sig?: typeof IOTA
    readonly wireScopes?: readonly string[]
  } = {},
): DiagramParts {
  const region = opts.region ?? 'r0'
  const arity = opts.arity ?? wireIds.length
  const regions = region === 'r0'
    ? sheet
    : { ...sheet, [region]: { kind: 'cut' as const, parent: 'r0' } }
  const nodes: Record<string, DiagramNode> = {
    eq: { kind: 'identity', region, sig: opts.sig ?? IOTA, arity },
  }
  for (const [index, wire] of wireIds.entries()) {
    nodes[`${wire}_pin`] = pin(opts.wireScopes?.[index] ?? region)
  }
  return {
    root: 'r0',
    regions,
    nodes,
    wires: Object.fromEntries(wireIds.map((wire, index) => [
      wire,
      {
        sig: IOTA,
        endpoints: [
          { node: 'eq', port: { kind: 'identity' as const, index } },
          pinEnd(`${wire}_pin`),
        ],
      },
    ])),
  }
}

describe('identity diagram nodes', () => {
  it('accepts an unordered homogeneous identity with at least two incidences', () => {
    const diagram = mkDiagram(identityParts(['a', 'b'], {
      region: 'r1',
      wireScopes: ['r0', 'r0'],
    }))

    expect(diagram.nodes.eq).toEqual({
      kind: 'identity',
      region: 'r1',
      sig: IOTA,
      arity: 2,
    })
    expect(diagram.wires.a?.endpoints).toContainEqual({
      node: 'eq',
      port: { kind: 'identity', index: 0 },
    })
    expect(diagram.wires.b?.endpoints).toContainEqual({
      node: 'eq',
      port: { kind: 'identity', index: 1 },
    })
  })

  // NEEDS-ADJUDICATION: the first clause requires identity arity ≥ 2. Arity
  // 1 is now a pin and arity 0 a typed point, both legal.
  it('rejects arity below two, missing incidences, and mixed wire signatures', () => {
    expect(() => mkDiagram(identityParts(['a'], { arity: 1 })))
      .toThrowError(/identity node 'eq' arity.*at least 2/i)

    expect(() => mkDiagram(identityParts(['a'], { arity: 2 })))
      .toThrowError(/port 'i:1'.*not attached/i)

    const mixed = identityParts(['a', 'b']) as {
      wires: Record<string, { sig: unknown }>
    } & DiagramParts
    mixed.wires.b!.sig = relSig([])
    expect(() => mkDiagram(mixed))
      .toThrowError(/wire 'b' sig.*does not match port 'i:1'/i)
  })

  it('drops an identity whose incidences all reach one distinct wire', () => {
    const normalized = mkDiagram({
      root: 'r0',
      regions: sheet,
      nodes: {
        eq: { kind: 'identity', region: 'r0', sig: IOTA, arity: 2 },
      },
      wires: {
        a: {
          sig: IOTA,
          endpoints: [
            { node: 'eq', port: { kind: 'identity', index: 0 } },
            { node: 'eq', port: { kind: 'identity', index: 1 } },
          ],
        },
      },
    })

    expect(normalized.nodes).toEqual({})
    expect(normalized.wires.a?.endpoints).toEqual([])
  })

  it('collapses a co-scoped identity to the lexicographically first wire', () => {
    const parts = identityParts(['b', 'a'])
    const normalized = mkDiagram(parts)

    expect(Object.keys(normalized.nodes)).not.toContain('eq')
    expect(Object.keys(normalized.wires)).toContain('a')
    expect(Object.keys(normalized.wires)).not.toContain('b')
  })

  it('composes wire transport across multiple deterministic collapses', () => {
    const normalized = mkDiagram({
      root: 'r0',
      regions: sheet,
      nodes: {
        eq1: { kind: 'identity', region: 'r0', sig: IOTA, arity: 2 },
        eq2: { kind: 'identity', region: 'r0', sig: IOTA, arity: 2 },
        c_pin: pin('r0'),
        a_pin: pin('r0'),
      },
      wires: {
        c: {
          sig: IOTA,
          endpoints: [
            { node: 'eq1', port: { kind: 'identity', index: 1 } },
            pinEnd('c_pin'),
          ],
        },
        b: {
          sig: IOTA,
          endpoints: [
            { node: 'eq1', port: { kind: 'identity', index: 0 } },
            { node: 'eq2', port: { kind: 'identity', index: 1 } },
          ],
        },
        a: {
          sig: IOTA,
          endpoints: [
            { node: 'eq2', port: { kind: 'identity', index: 0 } },
            pinEnd('a_pin'),
          ],
        },
      },
    })

    expect(Object.keys(normalized.wires)).toEqual(['a'])
  })

  it('collapses a one-outer identity onto the outer wire (one-point rule)', () => {
    // ∃x@r1 (x = b ∧ P(x)) ≡ P(b): the identity carries one wire scoped
    // above its region; every co-scoped wire's content lands on that wire.
    const normalized = mkDiagram({
      root: 'r0',
      regions: {
        ...sheet,
        r1: { kind: 'cut' as const, parent: 'r0' },
      },
      nodes: {
        eq: { kind: 'identity', region: 'r1', sig: IOTA, arity: 2 },
        p: { kind: 'atom', region: 'r1', sig: relSig([IOTA]) },
        b_pin: pin('r0'),
        head_pin: { kind: 'identity', region: 'r1', sig: relSig([IOTA]), arity: 1 },
      },
      wires: {
        b: {
          sig: IOTA,
          endpoints: [
            { node: 'eq', port: { kind: 'identity', index: 0 } },
            pinEnd('b_pin'),
          ],
        },
        head: {
          sig: relSig([IOTA]),
          endpoints: [
            { node: 'p', port: { kind: 'head' } },
            pinEnd('head_pin'),
          ],
        },
        x: {
          sig: IOTA,
          endpoints: [
            { node: 'eq', port: { kind: 'identity', index: 1 } },
            { node: 'p', port: { kind: 'arg', index: 0 } },
          ],
        },
      },
    })

    expect(Object.keys(normalized.nodes)).not.toContain('eq')
    expect(Object.keys(normalized.wires)).not.toContain('x')
    expect(normalized.wires.b!.endpoints).toContainEqual(
      { node: 'p', port: { kind: 'arg', index: 0 } },
    )
  })

  it('keeps an identity when two or more attached wires are scoped above its region', () => {
    const normalized = mkDiagram(identityParts(['a', 'b'], {
      region: 'r1',
      wireScopes: ['r0', 'r0'],
    }))

    expect(normalized.nodes.eq?.kind).toBe('identity')
    expect(Object.keys(normalized.wires).sort()).toEqual(['a', 'b'])
  })

  it('fuses same-region identities sharing a wire and reaches a fixpoint', () => {
    const normalized = mkDiagram({
      root: 'r0',
      regions: {
        r0: { kind: 'sheet' },
        r1: { kind: 'cut', parent: 'r0' },
      },
      nodes: {
        eqB: { kind: 'identity', region: 'r1', sig: IOTA, arity: 2 },
        eqA: { kind: 'identity', region: 'r1', sig: IOTA, arity: 2 },
        eqC: { kind: 'identity', region: 'r1', sig: IOTA, arity: 2 },
        a_pin: pin('r0'),
        z_pin: pin('r0'),
      },
      wires: {
        a: {
          sig: IOTA,
          endpoints: [
            { node: 'eqA', port: { kind: 'identity', index: 0 } },
            pinEnd('a_pin'),
          ],
        },
        sharedAB: {
          sig: IOTA,
          endpoints: [
            { node: 'eqA', port: { kind: 'identity', index: 1 } },
            { node: 'eqB', port: { kind: 'identity', index: 0 } },
          ],
        },
        sharedBC: {
          sig: IOTA,
          endpoints: [
            { node: 'eqB', port: { kind: 'identity', index: 1 } },
            { node: 'eqC', port: { kind: 'identity', index: 0 } },
          ],
        },
        z: {
          sig: IOTA,
          endpoints: [
            { node: 'eqC', port: { kind: 'identity', index: 1 } },
            pinEnd('z_pin'),
          ],
        },
      },
    })

    expect(Object.keys(normalized.nodes)).toEqual(['eqA'])
    expect(normalized.nodes.eqA).toMatchObject({ kind: 'identity', arity: 4 })
    expect(Object.keys(normalized.wires).sort()).toEqual(['a', 'sharedAB', 'sharedBC', 'z'])
    for (const wire of Object.values(normalized.wires)) {
      expect(wire.endpoints).toHaveLength(1)
      expect(wire.endpoints[0]?.node).toBe('eqA')
    }
  })

  it('does not fuse identity nodes in different regions', () => {
    const diagram = mkDiagram({
      root: 'r0',
      regions: {
        r0: { kind: 'sheet' },
        r1: { kind: 'cut', parent: 'r0' },
        r2: { kind: 'cut', parent: 'r0' },
      },
      nodes: {
        eqA: { kind: 'identity', region: 'r1', sig: IOTA, arity: 2 },
        eqB: { kind: 'identity', region: 'r2', sig: IOTA, arity: 2 },
        a_pin: pin('r0'),
        b_pin: pin('r0'),
      },
      wires: {
        a: {
          sig: IOTA,
          endpoints: [
            { node: 'eqA', port: { kind: 'identity', index: 0 } },
            pinEnd('a_pin'),
          ],
        },
        shared: {
          sig: IOTA,
          endpoints: [
            { node: 'eqA', port: { kind: 'identity', index: 1 } },
            { node: 'eqB', port: { kind: 'identity', index: 0 } },
          ],
        },
        b: {
          sig: IOTA,
          endpoints: [
            { node: 'eqB', port: { kind: 'identity', index: 1 } },
            pinEnd('b_pin'),
          ],
        },
      },
    })

    expect(Object.keys(diagram.nodes).sort())
      .toEqual(['a_pin', 'b_pin', 'eqA', 'eqB'])
  })

  it('canonicalizes port permutations to one explore form', () => {
    const make = (swap: boolean) => mkDiagram({
      root: 'r0',
      regions: {
        r0: { kind: 'sheet' },
        r1: { kind: 'cut', parent: 'r0' },
        r2: { kind: 'cut', parent: 'r1' },
      },
      nodes: {
        eq: { kind: 'identity', region: 'r2', sig: IOTA, arity: 2 },
        outer_pin: pin('r0'),
        inner_pin: pin('r1'),
      },
      wires: {
        outer: {
          sig: IOTA,
          endpoints: [
            { node: 'eq', port: { kind: 'identity', index: swap ? 1 : 0 } },
            pinEnd('outer_pin'),
          ],
        },
        inner: {
          sig: IOTA,
          endpoints: [
            { node: 'eq', port: { kind: 'identity', index: swap ? 0 : 1 } },
            pinEnd('inner_pin'),
          ],
        },
      },
    })

    expect(exploreForm(make(false))).toBe(exploreForm(make(true)))
  })

  it('round-trips identity JSON and rejects term/body node JSON', () => {
    const diagram = mkDiagram(identityParts(['a', 'b'], {
      region: 'r1',
      wireScopes: ['r0', 'r0'],
    }))
    const json = diagramToJson(diagram) as {
      nodes: Record<string, unknown>
      wires: Record<string, { endpoints: { port: string }[] }>
    }

    expect(json.nodes.eq).toEqual({
      kind: 'identity',
      region: 'r1',
      sig: { kind: 'iota' },
      arity: 2,
    })
    expect(json.wires.a?.endpoints[0]?.port).toBe('i:0')
    expect(diagramFromJson(JSON.parse(JSON.stringify(json)))).toEqual(diagram)

    for (const legacy of [
      { kind: 'term', region: 'r1', term: '#0', freePorts: [] },
      { kind: 'body', region: 'r1', sig: { kind: 'rel', args: [] }, content: {} },
    ]) {
      const rejected = JSON.parse(JSON.stringify(json)) as { nodes: Record<string, unknown> }
      rejected.nodes.eq = legacy
      expect(() => diagramFromJson(rejected)).toThrowError(/node 'eq' has unrecognized shape/i)
    }
  })
})
