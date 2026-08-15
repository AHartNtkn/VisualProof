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
    const instance = { kind: 'point', node: 'pt', region: 'cut', sig: IOTA } as const
    const inserted = applyVacuityInsert(base, instance)
    expect(inserted.nodes.pt).toEqual({ kind: 'identity', region: 'cut', sig: IOTA, arity: 0 })
    const removed = applyVacuityDelete(inserted, instance)
    expect(Object.keys(removed.nodes)).toHaveLength(0)
  })

  it('grows a bare two-point segment as point-then-stub, and retracts it', () => {
    const base = mkDiagram({ root: 'r0', regions: { r0: { kind: 'sheet' } } })
    const pointed = applyVacuityInsert(base, {
      kind: 'point', node: 'end1', region: 'r0', sig: IOTA,
    })
    const inserted = applyVacuityInsert(pointed, {
      kind: 'stub', base: 'end1', wire: 'w', end: 'end2', region: 'r0',
    })
    expect(derivedScope(inserted, 'w')).toBe('r0')
    expect(inserted.wires.w!.endpoints).toHaveLength(2)
    const retracted = applyVacuityDelete(inserted, {
      kind: 'stub', base: 'end1', wire: 'w', end: 'end2', region: 'r0',
    })
    const removed = applyVacuityDelete(retracted, {
      kind: 'point', node: 'end1', region: 'r0', sig: IOTA,
    })
    expect(Object.keys(removed.wires)).toHaveLength(0)
    expect(Object.keys(removed.nodes)).toHaveLength(0)
  })

  it('grows a stub out of an already-wired node, in one step', () => {
    const start = collapseFixture()
    const instance = {
      kind: 'stub', base: 'eq', wire: 'stub', end: 'tip', region: 'r0',
    } as const
    const grown = applyVacuityInsert(start, instance)
    expect((grown.nodes.eq as { arity: number }).arity).toBe(3)
    expect(derivedScope(grown, 'stub')).toBe('r0')
    const back = applyVacuityDelete(grown, instance)
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
      kind: 'stub', base: 'deep', wire: 'w', end: 'tip', region: 'r0',
    })).toThrow(/gated quantifier movement/)
  })

  it('refuses to retract a two-end wire whose far pin holds the quantifier above the base', () => {
    // pin at the sheet, base node inside the cut: the wire's quantifier
    // lives at the sheet — retracting it as a stub would erase that
    // quantifier position, which is join/sever territory.
    const d = mkDiagram({
      root: 'r0',
      regions: { r0: { kind: 'sheet' }, cut: { kind: 'cut', parent: 'r0' } },
      nodes: {
        deep: { kind: 'identity', region: 'cut', sig: IOTA, arity: 2 },
        e1: { kind: 'identity', region: 'cut', sig: IOTA, arity: 1 },
        high: { kind: 'identity', region: 'r0', sig: IOTA, arity: 1 },
      },
      wires: {
        x: {
          sig: IOTA,
          endpoints: [
            { node: 'deep', port: { kind: 'identity', index: 0 } },
            { node: 'e1', port: { kind: 'identity', index: 0 } },
          ],
        },
        w: {
          sig: IOTA,
          endpoints: [
            { node: 'deep', port: { kind: 'identity', index: 1 } },
            { node: 'high', port: { kind: 'identity', index: 0 } },
          ],
        },
      },
    })
    expect(() => applyVacuityDelete(d, {
      kind: 'stub', base: 'deep', wire: 'w', end: 'high', region: 'r0',
    })).toThrow(/join\/sever/)
  })

  it('attaches a pin only where the wire is visible', () => {
    const d = collapseFixture()
    const pinned = applyVacuityInsert(d, {
      kind: 'pin', wire: 's', node: 'pin', region: 'cut',
    })
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
      kind: 'pin', wire: 'a', node: 'pin', region: 'other',
    })).toThrow(/not visible/)
  })

  it('refuses to detach a load-bearing pin, and a last-but-one end', () => {
    const d = collapseFixture()
    // qpin is qhead's second end at the sheet: detaching it would leave one end.
    expect(() => applyVacuityDelete(d, {
      kind: 'pin', wire: 'qhead', node: 'qpin', region: 'r0',
    })).toThrow(/end/)
    // Pin s at the sheet twice, then drop one of them freely; the ORIGINAL
    // sheet position (the eq node) still holds the scope, so this succeeds —
    // but detaching the pin that alone holds a scope is refused.
    const deepOnly = mkDiagram({
      root: 'r0',
      regions: { r0: { kind: 'sheet' }, cut: { kind: 'cut', parent: 'r0' } },
      nodes: {
        p: { kind: 'atom', region: 'cut', sig: P },
        hold: { kind: 'identity', region: 'r0', sig: IOTA, arity: 1 },
        deeppin: { kind: 'identity', region: 'cut', sig: IOTA, arity: 1 },
        hpin: { kind: 'identity', region: 'cut', sig: P, arity: 1 },
      },
      wires: {
        a: {
          sig: IOTA,
          endpoints: [
            { node: 'p', port: { kind: 'arg', index: 0 } },
            { node: 'hold', port: { kind: 'identity', index: 0 } },
            { node: 'deeppin', port: { kind: 'identity', index: 0 } },
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
    expect(() => applyVacuityDelete(deepOnly, {
      kind: 'pin', wire: 'a', node: 'hold', region: 'r0',
    })).toThrow(/load-bearing/)
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
