import { describe, expect, it } from 'vitest'
import {
  mkDiagram,
  type DiagramNode,
  type DiagramParts,
  type Endpoint,
} from '../../../src/kernel/diagram/diagram'
import { sameDiagram } from '../../../src/kernel/diagram/canonical/iso'
import { diagramFromJson, diagramToJson } from '../../../src/kernel/diagram/json'
import { derivedScope } from '../../../src/kernel/diagram/regions'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
import {
  applyIdentification,
  applyPresentation,
  applyVacuityDelete,
} from '../../../src/kernel/rules/identity-rules'

const sheet = { r0: { kind: 'sheet' as const } }

// Identity nodes persist through construction: mkDiagram validates and
// freezes, and nothing rewrites equality apparatus behind the proof's back.
// Every shape the deleted eager normalizer used to reach silently is reached
// here by the explicit rule step that licenses it — identification for the
// one-point merges, presentation invariance for same-region fusion — and the
// shapes it used to reach unsoundly (a wire left with fewer than two ends)
// are refusals.

/** A pin: the node holding a wire's free end, and its quantifier, at `region`. */
function pin(region: string): DiagramNode {
  return { kind: 'identity', region, sig: IOTA, arity: 1 }
}

function pinEnd(node: string): Endpoint {
  return { node, port: { kind: 'identity', index: 0 } }
}

function identityEnd(node: string, index: number): Endpoint {
  return { node, port: { kind: 'identity', index } }
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
          identityEnd('eq', index),
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

  it('accepts nullary points and unary pins, and rejects missing incidences and mixed wire signatures', () => {
    // Arity 0 is the typed point ∃x:σ.⊤; arity 1 is a pin, whose whole
    // effect is to hold its wire's quantifier at its own region.
    const point = mkDiagram(identityParts([], { arity: 0 }))
    expect(point.nodes.eq).toEqual({ kind: 'identity', region: 'r0', sig: IOTA, arity: 0 })

    const pinned = mkDiagram(identityParts(['a'], { arity: 1 }))
    expect(pinned.nodes.eq).toEqual({ kind: 'identity', region: 'r0', sig: IOTA, arity: 1 })
    expect(pinned.wires.a?.endpoints).toHaveLength(2)

    expect(() => mkDiagram(identityParts(['a'], { arity: 2 })))
      .toThrowError(/port 'i:1'.*not attached/i)

    const mixed = identityParts(['a', 'b']) as {
      wires: Record<string, { sig: unknown }>
    } & DiagramParts
    mixed.wires.b!.sig = relSig([])
    expect(() => mkDiagram(mixed))
      .toThrowError(/wire 'b' sig.*does not match port 'i:1'/i)
  })

  it('keeps an identity looped onto one wire and refuses to contract its last-but-one end', () => {
    // The wire's only two ends are two ports of `eq`. The deleted eager
    // rewrite dropped the node here and left an endpoint-free wire; a wire
    // end is a node, so removing either port is now a refusal.
    const looped = mkDiagram({
      root: 'r0',
      regions: sheet,
      nodes: {
        eq: { kind: 'identity', region: 'r0', sig: IOTA, arity: 2 },
      },
      wires: {
        a: {
          sig: IOTA,
          endpoints: [identityEnd('eq', 0), identityEnd('eq', 1)],
        },
      },
    })

    expect(looped.nodes.eq).toEqual({ kind: 'identity', region: 'r0', sig: IOTA, arity: 2 })
    expect(looped.wires.a?.endpoints).toEqual([identityEnd('eq', 0), identityEnd('eq', 1)])

    expect(() => applyPresentation(looped, {
      region: 'r0',
      removeNodes: ['eq'],
      addNodes: { contracted: ['a'] },
    })).toThrowError(/at least two/i)
  })

  it('collapses a co-scoped identity onto a chosen survivor by an explicit identification', () => {
    const built = mkDiagram(identityParts(['b', 'a']))
    expect(built.nodes.eq).toEqual({ kind: 'identity', region: 'r0', sig: IOTA, arity: 2 })
    expect(Object.keys(built.wires).sort()).toEqual(['a', 'b'])

    const collapsed = applyIdentification(built, {
      kind: 'collapse',
      node: 'eq',
      survivor: 'a',
      absorbed: ['b'],
    })

    expect(Object.keys(collapsed.wires)).toEqual(['a'])
    // The node outlives the merge, shrunk by the absorbed port — that port on
    // the survivor is what makes scope preservation a theorem.
    expect(collapsed.nodes.eq).toEqual({ kind: 'identity', region: 'r0', sig: IOTA, arity: 1 })
    expect(collapsed.wires.a?.endpoints).toContainEqual(pinEnd('b_pin'))
    expect(derivedScope(collapsed, 'a')).toBe('r0')

    // Finishing the old normalizer's macro: the leftover pin detaches,
    // because the survivor still has its two real ends.
    const detached = applyVacuityDelete(collapsed, {
      nodes: { eq: { region: 'r0', sig: IOTA, arity: 1 } },
      wires: {},
      attachments: { a: [identityEnd('eq', 0)] },
    })
    expect(Object.keys(detached.nodes).sort()).toEqual(['a_pin', 'b_pin'])
    expect(Object.keys(detached.wires)).toEqual(['a'])
  })

  it('composes explicit collapses along a chain of identities, keeping wire ids stable', () => {
    // c —eq1— b —eq2— a, everything at the root: two one-point steps merge
    // the chain onto `a`. No rule renames a wire it does not delete, so the
    // survivor keeps its id across both steps (what the deleted wire-image
    // transport used to launder).
    const chain = mkDiagram({
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
          endpoints: [identityEnd('eq1', 1), pinEnd('c_pin')],
        },
        b: {
          sig: IOTA,
          endpoints: [identityEnd('eq1', 0), identityEnd('eq2', 1)],
        },
        a: {
          sig: IOTA,
          endpoints: [identityEnd('eq2', 0), pinEnd('a_pin')],
        },
      },
    })

    const first = applyIdentification(chain, {
      kind: 'collapse',
      node: 'eq2',
      survivor: 'a',
      absorbed: ['b'],
    })
    expect(Object.keys(first.wires).sort()).toEqual(['a', 'c'])
    expect(first.wires.a?.endpoints).toContainEqual(identityEnd('eq1', 0))

    const second = applyIdentification(first, {
      kind: 'collapse',
      node: 'eq1',
      survivor: 'a',
      absorbed: ['c'],
    })

    expect(Object.keys(second.wires)).toEqual(['a'])
    expect(second.wires.a?.endpoints).toContainEqual(pinEnd('c_pin'))
    expect(second.wires.a?.endpoints).toContainEqual(pinEnd('a_pin'))
    expect(derivedScope(second, 'a')).toBe('r0')
  })

  it('collapses a one-outer identity onto the outer wire (one-point rule)', () => {
    // ∃x@r1 (x = b ∧ P(x)) ≡ P(b): the identity carries one wire whose
    // derived scope is above its region; the co-scoped wire's content lands
    // on that wire and the outer wire's scope is untouched.
    const diagram = mkDiagram({
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
          endpoints: [identityEnd('eq', 0), pinEnd('b_pin')],
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
            identityEnd('eq', 1),
            { node: 'p', port: { kind: 'arg', index: 0 } },
          ],
        },
      },
    })

    expect(derivedScope(diagram, 'b')).toBe('r0')
    expect(derivedScope(diagram, 'x')).toBe('r1')

    const collapsed = applyIdentification(diagram, {
      kind: 'collapse',
      node: 'eq',
      survivor: 'b',
      absorbed: ['x'],
    })

    expect(Object.keys(collapsed.wires)).not.toContain('x')
    expect(collapsed.wires.b!.endpoints).toContainEqual(
      { node: 'p', port: { kind: 'arg', index: 0 } },
    )
    expect(collapsed.nodes.eq).toEqual({ kind: 'identity', region: 'r1', sig: IOTA, arity: 1 })
    expect(derivedScope(collapsed, 'b')).toBe('r0')
  })

  it('refuses to collapse a wire whose quantifier sits above the equality', () => {
    // The mirror of the case above: absorbing the OUTER wire would move a
    // quantifier inward, which is join/sever's gated business, not the
    // one-point rule's.
    const diagram = mkDiagram(identityParts(['a', 'b'], {
      region: 'r1',
      wireScopes: ['r0', 'r1'],
    }))

    expect(() => applyIdentification(diagram, {
      kind: 'collapse',
      node: 'eq',
      survivor: 'b',
      absorbed: ['a'],
    })).toThrowError(/quantifier does not sit where it is equated/)
  })

  it('fuses same-region identities sharing a wire in one presentation step', () => {
    const diagram = mkDiagram({
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
          endpoints: [identityEnd('eqA', 0), pinEnd('a_pin')],
        },
        sharedAB: {
          sig: IOTA,
          endpoints: [identityEnd('eqA', 1), identityEnd('eqB', 0)],
        },
        sharedBC: {
          sig: IOTA,
          endpoints: [identityEnd('eqB', 1), identityEnd('eqC', 0)],
        },
        z: {
          sig: IOTA,
          endpoints: [identityEnd('eqC', 1), pinEnd('z_pin')],
        },
      },
    })

    // Construction fuses nothing; the three nodes are what the author wrote.
    expect(Object.keys(diagram.nodes).sort())
      .toEqual(['a_pin', 'eqA', 'eqB', 'eqC', 'z_pin'])

    // Fusion is the port UNION, multiplicities preserved: the shared wires
    // become loops on the fused node, so no wire loses an end.
    const fused = applyPresentation(diagram, {
      region: 'r1',
      removeNodes: ['eqA', 'eqB', 'eqC'],
      addNodes: { eq: ['a', 'sharedAB', 'sharedAB', 'sharedBC', 'sharedBC', 'z'] },
    })

    expect(Object.keys(fused.nodes).sort()).toEqual(['a_pin', 'eq', 'z_pin'])
    expect(fused.nodes.eq).toMatchObject({ kind: 'identity', region: 'r1', arity: 6 })
    expect(Object.keys(fused.wires).sort()).toEqual(['a', 'sharedAB', 'sharedBC', 'z'])
    for (const wire of Object.values(fused.wires)) {
      expect(wire.endpoints).toHaveLength(2)
    }
    for (const shared of ['sharedAB', 'sharedBC']) {
      expect(fused.wires[shared]!.endpoints.map((end) => end.node)).toEqual(['eq', 'eq'])
    }
    // Every derived scope is fixed, which is what makes fusion ungated.
    for (const [wireId, scope] of [['a', 'r0'], ['sharedAB', 'r1'], ['sharedBC', 'r1'], ['z', 'r0']] as const) {
      expect(derivedScope(fused, wireId)).toBe(scope)
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
          endpoints: [identityEnd('eqA', 0), pinEnd('a_pin')],
        },
        shared: {
          sig: IOTA,
          endpoints: [identityEnd('eqA', 1), identityEnd('eqB', 0)],
        },
        b: {
          sig: IOTA,
          endpoints: [identityEnd('eqB', 1), pinEnd('b_pin')],
        },
      },
    })

    expect(Object.keys(diagram.nodes).sort())
      .toEqual(['a_pin', 'b_pin', 'eqA', 'eqB'])
    expect(() => applyPresentation(diagram, {
      region: 'r1',
      removeNodes: ['eqA', 'eqB'],
      addNodes: { eq: ['a', 'shared', 'shared', 'b'] },
    })).toThrowError(/homed at 'r2', not 'r1'/)
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
            identityEnd('eq', swap ? 1 : 0),
            pinEnd('outer_pin'),
          ],
        },
        inner: {
          sig: IOTA,
          endpoints: [
            identityEnd('eq', swap ? 0 : 1),
            pinEnd('inner_pin'),
          ],
        },
      },
    })

    expect(sameDiagram(make(false), make(true))).toBe(true)
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
