import { describe, expect, it } from 'vitest'
import type { Diagram } from '../../../src/kernel/diagram/diagram'
import { mkDiagram } from '../../../src/kernel/diagram/diagram'
import { derivedScope } from '../../../src/kernel/diagram/regions'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
import { applyDoubleCutIntro, applyDoubleCutElim } from '../../../src/kernel/rules/doublecut'
import { applyErasure } from '../../../src/kernel/rules/erasure'
import { applyVacuityInsert } from '../../../src/kernel/rules/identity-rules'
import { applyEndsDelete } from '../../../src/kernel/rules/wire-content'
import { applyWireSever } from '../../../src/kernel/rules/wire-quantifier'

const P = relSig([IOTA])

/** A(x) on the sheet, ¬P(x): x's quantifier reads at the sheet through A. */
function sheetAndCutFixture(): Diagram {
  return mkDiagram({
    root: 'r0',
    regions: { r0: { kind: 'sheet' }, cut: { kind: 'cut', parent: 'r0' } },
    nodes: {
      a: { kind: 'atom', region: 'r0', sig: P },
      p: { kind: 'atom', region: 'cut', sig: P },
      ah: { kind: 'identity', region: 'r0', sig: P, arity: 1 },
      ph: { kind: 'identity', region: 'cut', sig: P, arity: 1 },
    },
    wires: {
      x: {
        sig: IOTA,
        endpoints: [
          { node: 'a', port: { kind: 'arg', index: 0 } },
          { node: 'p', port: { kind: 'arg', index: 0 } },
        ],
      },
      ahead: {
        sig: P,
        endpoints: [
          { node: 'a', port: { kind: 'head' } },
          { node: 'ah', port: { kind: 'identity', index: 0 } },
        ],
      },
      phead: {
        sig: P,
        endpoints: [
          { node: 'p', port: { kind: 'head' } },
          { node: 'ph', port: { kind: 'identity', index: 0 } },
        ],
      },
    },
  })
}

describe('erasure scope precondition', () => {
  it('refuses to erase the incidence holding a quantifier out of a cut', () => {
    const d = sheetAndCutFixture()
    // Erasing A(x) would drop x's remaining incidence into the cut:
    // ∃x ¬P(x) would silently become ¬∃x P(x).
    expect(() => applyErasure(d, {
      region: 'r0',
      regions: [],
      nodes: ['a', 'ah'],
      wires: ['ahead'],
    })).toThrow(/pin it .*first|move the quantifier/)
  })

  it('erases the same content once the wire is pinned first', () => {
    const d = sheetAndCutFixture()
    const pinned = applyVacuityInsert(d, {
      nodes: { hold: { region: 'r0', sig: IOTA, arity: 1 } },
      wires: {},
      attachments: { x: [{ node: 'hold', port: { kind: 'identity', index: 0 } }] },
    })
    const erased = applyErasure(pinned, {
      region: 'r0',
      regions: [],
      nodes: ['a', 'ah'],
      wires: ['ahead'],
    })
    expect(erased.nodes.a).toBeUndefined()
    expect(derivedScope(erased, 'x')).toBe('r0')
  })
})

describe('double cut and quantifier positions', () => {
  it('intro deposits the pin that keeps a quantifier outside the new cuts', () => {
    const d = sheetAndCutFixture()
    const wrapped = applyDoubleCutIntro(d, {
      region: 'r0',
      regions: ['cut'],
      nodes: ['a', 'ah'],
      wires: ['ahead', 'x'],
    })
    // Every incidence of x moved inside the double cut; its quantifier must
    // still read at the sheet.
    expect(derivedScope(wrapped, 'x')).toBe('r0')
    expect(derivedScope(wrapped, 'ahead')).toBe('r0')
  })

  it('intro round-trips through elim, scopes intact', () => {
    const d = sheetAndCutFixture()
    const wrapped = applyDoubleCutIntro(d, {
      region: 'r0',
      regions: ['cut'],
      nodes: ['a', 'ah'],
      wires: ['ahead', 'x'],
    })
    const outer = Object.keys(wrapped.regions).find((rid) => {
      const region = wrapped.regions[rid]!
      return region.kind === 'cut' && region.parent === 'r0'
    })!
    const restored = applyDoubleCutElim(wrapped, outer)
    expect(derivedScope(restored, 'x')).toBe('r0')
    expect(derivedScope(restored, 'ahead')).toBe('r0')
  })

  it('elim refuses an annulus holding a pin — that pin is a quantifier', () => {
    const d = sheetAndCutFixture()
    const wrapped = applyDoubleCutIntro(d, {
      region: 'r0',
      regions: ['cut'],
      nodes: ['a', 'ah'],
      wires: ['ahead', 'x'],
    })
    const outer = Object.keys(wrapped.regions).find((rid) => {
      const region = wrapped.regions[rid]!
      return region.kind === 'cut' && region.parent === 'r0'
    })!
    const annulusPinned = applyVacuityInsert(wrapped, {
      nodes: { hold: { region: outer, sig: IOTA, arity: 1 } },
      wires: {},
      attachments: { x: [{ node: 'hold', port: { kind: 'identity', index: 0 } }] },
    })
    expect(() => applyDoubleCutElim(annulusPinned, outer)).toThrow(/nothing else/)
  })
})

describe('remnant completion', () => {
  it('sever completes both sides with pins at their declared scopes', () => {
    const d = sheetAndCutFixture()
    const severed = applyWireSever(d, {
      wire: 'x',
      keep: [{ node: 'a', port: { kind: 'arg', index: 0 } }],
    })
    // The remainder keeps A's end plus a completion pin at the old scope;
    // the split-off P-end wire lives at the old scope through its own pin.
    expect(derivedScope(severed, 'x')).toBe('r0')
    const fresh = Object.keys(severed.wires).find((w) => w.startsWith('x_sever'))!
    expect(derivedScope(severed, fresh)).toBe('r0')
    for (const wireId of Object.keys(severed.wires)) {
      expect(severed.wires[wireId]!.endpoints.length).toBeGreaterThanOrEqual(2)
    }
  })

  it("ends-delete leaves the bare two-pin segment, not an endpoint-free husk", () => {
    const base = mkDiagram({
      root: 'r0',
      regions: { r0: { kind: 'sheet' }, cut: { kind: 'cut', parent: 'r0' } },
      nodes: {
        p: { kind: 'atom', region: 'cut', sig: P },
        ppin: { kind: 'identity', region: 'cut', sig: IOTA, arity: 1 },
        hpin: { kind: 'identity', region: 'cut', sig: P, arity: 1 },
      },
      wires: {
        arg: {
          sig: IOTA,
          endpoints: [
            { node: 'p', port: { kind: 'arg', index: 0 } },
            { node: 'ppin', port: { kind: 'identity', index: 0 } },
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
    // P's argument wire needs its scope held before its endpoint erases.
    const prepared = applyVacuityInsert(base, {
      nodes: { hold: { region: 'cut', sig: IOTA, arity: 1 } },
      wires: {},
      attachments: { arg: [{ node: 'hold', port: { kind: 'identity', index: 0 } }] },
    })
    const deleted = applyEndsDelete(prepared, 'h')
    const husk = deleted.wires.h!
    expect(husk.endpoints.length).toBeGreaterThanOrEqual(2)
    for (const endpoint of husk.endpoints) {
      const node = deleted.nodes[endpoint.node]!
      expect(node.kind).toBe('identity')
    }
    expect(derivedScope(deleted, 'h')).toBe('cut')
  })
})
