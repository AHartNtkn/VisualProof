import { describe, expect, it } from 'vitest'
import type { Diagram } from '../../../src/kernel/diagram/diagram'
import { mkDiagram } from '../../../src/kernel/diagram/diagram'
import { derivedScope } from '../../../src/kernel/diagram/regions'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
import {
  applyIdentification,
  applyPresentation,
  applyVacuityDelete,
  applyVacuityInsert,
} from '../../../src/kernel/rules/identity-rules'

const P = relSig([IOTA])

/** Q(s) with s reaching a binary identity at the sheet; ¬P(a) with a equated to s there. */
function collapseFixture(): Diagram {
  return mkDiagram({
    root: 'r0',
    regions: { r0: { kind: 'sheet' }, cut: { kind: 'cut', parent: 'r0' } },
    nodes: {
      q: { kind: 'atom', region: 'r0', sig: P },
      p: { kind: 'atom', region: 'cut', sig: P },
      eq: { kind: 'identity', region: 'r0', sig: IOTA, arity: 2 },
      qpin: { kind: 'identity', region: 'r0', sig: P, arity: 1 },
      ppin: { kind: 'identity', region: 'cut', sig: P, arity: 1 },
    },
    wires: {
      s: {
        sig: IOTA,
        endpoints: [
          { node: 'q', port: { kind: 'arg', index: 0 } },
          { node: 'eq', port: { kind: 'identity', index: 0 } },
        ],
      },
      a: {
        sig: IOTA,
        endpoints: [
          { node: 'p', port: { kind: 'arg', index: 0 } },
          { node: 'eq', port: { kind: 'identity', index: 1 } },
        ],
      },
      qhead: {
        sig: P,
        endpoints: [
          { node: 'q', port: { kind: 'head' } },
          { node: 'qpin', port: { kind: 'identity', index: 0 } },
        ],
      },
      phead: {
        sig: P,
        endpoints: [
          { node: 'p', port: { kind: 'head' } },
          { node: 'ppin', port: { kind: 'identity', index: 0 } },
        ],
      },
    },
  })
}

describe('vacuity', () => {
  it('introduces and eliminates a typed point anywhere, including inside a cut', () => {
    const base = mkDiagram({
      root: 'r0',
      regions: { r0: { kind: 'sheet' }, cut: { kind: 'cut', parent: 'r0' } },
    })
    const assembly = {
      nodes: { pt: { region: 'cut', sig: IOTA, arity: 0 } },
      wires: {},
      attachments: {},
    }
    const inserted = applyVacuityInsert(base, assembly)
    expect(inserted.nodes.pt).toEqual({ kind: 'identity', region: 'cut', sig: IOTA, arity: 0 })
    const removed = applyVacuityDelete(inserted, assembly)
    expect(Object.keys(removed.nodes)).toHaveLength(0)
  })

  it('grows a bare two-point segment (the drawable floating existential)', () => {
    const base = mkDiagram({ root: 'r0', regions: { r0: { kind: 'sheet' } } })
    const assembly = {
      nodes: {
        end1: { region: 'r0', sig: IOTA, arity: 1 },
        end2: { region: 'r0', sig: IOTA, arity: 1 },
      },
      wires: {
        w: {
          sig: IOTA,
          endpoints: [
            { node: 'end1', port: { kind: 'identity', index: 0 } as const },
            { node: 'end2', port: { kind: 'identity', index: 0 } as const },
          ],
        },
      },
      attachments: {},
    }
    const inserted = applyVacuityInsert(base, assembly)
    expect(derivedScope(inserted, 'w')).toBe('r0')
    const removed = applyVacuityDelete(inserted, assembly)
    expect(Object.keys(removed.wires)).toHaveLength(0)
    expect(Object.keys(removed.nodes)).toHaveLength(0)
  })

  it('grows a stub out of an already-wired node, in one step', () => {
    const start = collapseFixture()
    const assembly = {
      nodes: { tip: { region: 'r0', sig: IOTA, arity: 1 } },
      wires: {
        stub: {
          sig: IOTA,
          endpoints: [
            // A new port on the existing binary node, extending its arity.
            { node: 'eq', port: { kind: 'identity', index: 2 } as const },
            { node: 'tip', port: { kind: 'identity', index: 0 } as const },
          ],
        },
      },
      attachments: {},
    }
    const grown = applyVacuityInsert(start, assembly)
    expect((grown.nodes.eq as { arity: number }).arity).toBe(3)
    expect(derivedScope(grown, 'stub')).toBe('r0')
    const back = applyVacuityDelete(grown, {
      ...assembly,
      nodes: { tip: { region: 'r0', sig: IOTA, arity: 1 } },
    })
    expect((back.nodes.eq as { arity: number }).arity).toBe(2)
    expect(back.wires.stub).toBeUndefined()
  })

  it('refuses a stub whose point sits above its equality (quantifier above the cut)', () => {
    const base = mkDiagram({
      root: 'r0',
      regions: { r0: { kind: 'sheet' }, cut: { kind: 'cut', parent: 'r0' } },
      nodes: {
        deep: { kind: 'identity', region: 'cut', sig: IOTA, arity: 2 },
        e1: { kind: 'identity', region: 'cut', sig: IOTA, arity: 1 },
        e2: { kind: 'identity', region: 'cut', sig: IOTA, arity: 1 },
      },
      wires: {
        x: {
          sig: IOTA,
          endpoints: [
            { node: 'deep', port: { kind: 'identity', index: 0 } },
            { node: 'e1', port: { kind: 'identity', index: 0 } },
          ],
        },
        y: {
          sig: IOTA,
          endpoints: [
            { node: 'deep', port: { kind: 'identity', index: 1 } },
            { node: 'e2', port: { kind: 'identity', index: 0 } },
          ],
        },
      },
    })
    expect(() => applyVacuityInsert(base, {
      nodes: { tip: { region: 'r0', sig: IOTA, arity: 1 } },
      wires: {
        w: {
          sig: IOTA,
          endpoints: [
            { node: 'deep', port: { kind: 'identity', index: 2 } },
            { node: 'tip', port: { kind: 'identity', index: 0 } },
          ],
        },
      },
      attachments: {},
    })).toThrow(/not ⊤-shaped/)
  })

  it('attaches a pin only where the wire is visible', () => {
    const d = collapseFixture()
    const pinDeep = {
      nodes: { pin: { region: 'cut', sig: IOTA, arity: 1 } },
      wires: {},
      attachments: { s: [{ node: 'pin', port: { kind: 'identity', index: 0 } as const }] },
    }
    const pinned = applyVacuityInsert(d, pinDeep)
    expect(derivedScope(pinned, 's')).toBe('r0')

    const sOnly = mkDiagram({
      root: 'r0',
      regions: {
        r0: { kind: 'sheet' },
        cut: { kind: 'cut', parent: 'r0' },
        other: { kind: 'cut', parent: 'r0' },
      },
      nodes: {
        p: { kind: 'atom', region: 'cut', sig: P },
        apin: { kind: 'identity', region: 'cut', sig: IOTA, arity: 1 },
        hpin: { kind: 'identity', region: 'cut', sig: P, arity: 1 },
      },
      wires: {
        a: {
          sig: IOTA,
          endpoints: [
            { node: 'p', port: { kind: 'arg', index: 0 } },
            { node: 'apin', port: { kind: 'identity', index: 0 } },
          ],
        },
        h: {
          sig: P,
          endpoints: [
            { node: 'p', port: { kind: 'head' } },
            { node: 'hpin', port: { kind: 'identity', index: 0 } },
          ],
        },
      },
    })
    expect(() => applyVacuityInsert(sOnly, {
      nodes: { pin: { region: 'other', sig: IOTA, arity: 1 } },
      wires: {},
      attachments: { a: [{ node: 'pin', port: { kind: 'identity', index: 0 } }] },
    })).toThrow(/not visible/)
  })

  it('refuses to detach a load-bearing pin, and a last-but-one end', () => {
    const d = collapseFixture()
    // ppin holds phead's quantifier inside the cut and is also its second
    // end; qpin holds qhead at the sheet.
    expect(() => applyVacuityDelete(d, {
      nodes: { qpin: { region: 'r0', sig: P, arity: 1 } },
      wires: {},
      attachments: { qhead: [{ node: 'qpin', port: { kind: 'identity', index: 0 } }] },
    })).toThrow(/end/)
  })

  it('refuses an assembly component bridging two existing wires', () => {
    const d = collapseFixture()
    expect(() => applyVacuityInsert(d, {
      nodes: { bridge: { region: 'r0', sig: IOTA, arity: 2 } },
      wires: {},
      attachments: {
        s: [{ node: 'bridge', port: { kind: 'identity', index: 0 } }],
        a: [{ node: 'bridge', port: { kind: 'identity', index: 1 } }],
      },
    })).toThrow(/gated insertion/)
  })
})

describe('presentation invariance', () => {
  /** x=s and s=y as two binary nodes inside one cut, wires pinned at the sheet. */
  function chainFixture(): Diagram {
    return mkDiagram({
      root: 'r0',
      regions: { r0: { kind: 'sheet' }, cut: { kind: 'cut', parent: 'r0' } },
      nodes: {
        i1: { kind: 'identity', region: 'cut', sig: IOTA, arity: 2 },
        i2: { kind: 'identity', region: 'cut', sig: IOTA, arity: 2 },
        px: { kind: 'identity', region: 'r0', sig: IOTA, arity: 1 },
        ps: { kind: 'identity', region: 'r0', sig: IOTA, arity: 1 },
        py: { kind: 'identity', region: 'r0', sig: IOTA, arity: 1 },
      },
      wires: {
        x: {
          sig: IOTA,
          endpoints: [
            { node: 'px', port: { kind: 'identity', index: 0 } },
            { node: 'i1', port: { kind: 'identity', index: 0 } },
          ],
        },
        s: {
          sig: IOTA,
          endpoints: [
            { node: 'ps', port: { kind: 'identity', index: 0 } },
            { node: 'i1', port: { kind: 'identity', index: 1 } },
            { node: 'i2', port: { kind: 'identity', index: 0 } },
          ],
        },
        y: {
          sig: IOTA,
          endpoints: [
            { node: 'py', port: { kind: 'identity', index: 0 } },
            { node: 'i2', port: { kind: 'identity', index: 1 } },
          ],
        },
      },
    })
  }

  it('fuses a spanned chain into one node and back', () => {
    const d = chainFixture()
    const fused = applyPresentation(d, {
      region: 'cut',
      removeNodes: ['i1', 'i2'],
      addNodes: { big: ['x', 's', 'y'] },
    })
    expect(fused.nodes.i1).toBeUndefined()
    expect(fused.nodes.i2).toBeUndefined()
    expect((fused.nodes.big as { arity: number }).arity).toBe(3)
    expect(derivedScope(fused, 'x')).toBe('r0')
    expect(derivedScope(fused, 's')).toBe('r0')

    const split = applyPresentation(fused, {
      region: 'cut',
      removeNodes: ['big'],
      addNodes: { j1: ['x', 's'], j2: ['s', 'y'] },
    })
    expect((split.nodes.j1 as { arity: number }).arity).toBe(2)
    expect((split.nodes.j2 as { arity: number }).arity).toBe(2)
  })

  it('refuses a re-presentation that changes what is equal', () => {
    const d = chainFixture()
    expect(() => applyPresentation(d, {
      region: 'cut',
      removeNodes: ['i1', 'i2'],
      addNodes: { j1: ['x', 's'], j2: ['y'] },
    })).toThrow(/different\s+equalities/)
  })

  it('refuses nodes from another region', () => {
    const d = collapseFixture()
    expect(() => applyPresentation(d, {
      region: 'cut',
      removeNodes: ['eq'],
      addNodes: { z: ['s', 'a'] },
    })).toThrow(/homed at/)
  })
})

describe('identification', () => {
  it('collapses an absorbed wire onto the survivor; the node survives as a pin', () => {
    const d = collapseFixture()
    const result = applyIdentification(d, {
      kind: 'collapse',
      node: 'eq',
      survivor: 's',
      absorbed: ['a'],
    })
    expect(result.wires.a).toBeUndefined()
    const s = result.wires.s!
    const keys = s.endpoints.map((ep) => `${ep.node}:${ep.port.kind}`).sort()
    expect(keys).toEqual(['eq:identity', 'p:arg', 'q:arg'])
    expect((result.nodes.eq as { arity: number }).arity).toBe(1)
    expect(derivedScope(result, 's')).toBe('r0')
  })

  it('refuses to absorb a wire quantified outside the equality region', () => {
    // The equality sits inside the cut; s reaches Q at the sheet.
    const d = mkDiagram({
      root: 'r0',
      regions: { r0: { kind: 'sheet' }, cut: { kind: 'cut', parent: 'r0' } },
      nodes: {
        q: { kind: 'atom', region: 'r0', sig: P },
        p: { kind: 'atom', region: 'cut', sig: P },
        eq: { kind: 'identity', region: 'cut', sig: IOTA, arity: 2 },
        qpin: { kind: 'identity', region: 'r0', sig: P, arity: 1 },
        ppin: { kind: 'identity', region: 'cut', sig: P, arity: 1 },
      },
      wires: {
        s: {
          sig: IOTA,
          endpoints: [
            { node: 'q', port: { kind: 'arg', index: 0 } },
            { node: 'eq', port: { kind: 'identity', index: 0 } },
          ],
        },
        a: {
          sig: IOTA,
          endpoints: [
            { node: 'p', port: { kind: 'arg', index: 0 } },
            { node: 'eq', port: { kind: 'identity', index: 1 } },
          ],
        },
        qhead: {
          sig: P,
          endpoints: [
            { node: 'q', port: { kind: 'head' } },
            { node: 'qpin', port: { kind: 'identity', index: 0 } },
          ],
        },
        phead: {
          sig: P,
          endpoints: [
            { node: 'p', port: { kind: 'head' } },
            { node: 'ppin', port: { kind: 'identity', index: 0 } },
          ],
        },
      },
    })
    expect(() => applyIdentification(d, {
      kind: 'collapse',
      node: 'eq',
      survivor: 'a',
      absorbed: ['s'],
    })).toThrow(/outside the equality's region/)
  })

  it('exposure splits mentions onto a fresh equated wire and round-trips', () => {
    const collapsed = applyIdentification(collapseFixture(), {
      kind: 'collapse',
      node: 'eq',
      survivor: 's',
      absorbed: ['a'],
    })
    const exposed = applyIdentification(collapsed, {
      kind: 'expose',
      node: 'eq',
      survivor: 's',
      freshWire: 'a2',
      transfer: [{ node: 'p', port: { kind: 'arg', index: 0 } }],
    })
    expect(exposed.wires.a2).toBeDefined()
    expect((exposed.nodes.eq as { arity: number }).arity).toBe(2)
    expect(derivedScope(exposed, 'a2')).toBe('r0')
    expect(derivedScope(exposed, 's')).toBe('r0')
  })

  it('refuses an empty exposure — it would mint a one-ended wire', () => {
    const d = collapseFixture()
    expect(() => applyIdentification(d, {
      kind: 'expose',
      node: 'eq',
      survivor: 's',
      freshWire: 'w2',
      transfer: [],
    })).toThrow(/nonempty transfer/)
  })
})
