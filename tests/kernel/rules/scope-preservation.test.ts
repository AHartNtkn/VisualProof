import { describe, expect, it } from 'vitest'
import type { Diagram } from '../../../src/kernel/diagram/diagram'
import { mkDiagram } from '../../../src/kernel/diagram/diagram'
import { derivedScope } from '../../../src/kernel/diagram/regions'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
import { applyDoubleCutIntro, applyDoubleCutElim } from '../../../src/kernel/rules/doublecut'
import { applyErasure } from '../../../src/kernel/rules/erasure'
import { applyDeiteration, findDeiterationEvidence } from '../../../src/kernel/rules/iteration'
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

describe('erasure caps touched wires', () => {
  it('caps the wire whose quantifier the erased incidence held', () => {
    const d = sheetAndCutFixture()
    // Erasing A(x) would drop x's remaining incidence into the cut —
    // ∃x ¬P(x) silently becoming ¬∃x P(x). The rule caps instead of
    // refusing: a completion pin at x's pre-removal derived scope keeps
    // the quantifier where it was (Lean: Erasure.residue).
    const erased = applyErasure(d, {
      region: 'r0',
      regions: [],
      nodes: ['a', 'ah'],
      wires: ['ahead'],
    })
    expect(erased.nodes.a).toBeUndefined()
    expect(erased.wires.ahead).toBeUndefined()
    expect(derivedScope(erased, 'x')).toBe('r0')
    const x = erased.wires.x!
    expect(x.endpoints.length).toBeGreaterThanOrEqual(2)
    const cap = x.endpoints.find((ep) => {
      const node = erased.nodes[ep.node]!
      return node.kind === 'identity' && node.arity === 1 && node.region === 'r0'
    })
    expect(cap, 'a fresh pin at the old scope holds the quantifier').toBeDefined()
  })

  it('mints nothing when the wire is already held', () => {
    const d = sheetAndCutFixture()
    const pinned = applyVacuityInsert(d, {
      kind: 'pin', wire: 'x', node: 'hold', region: 'r0',
    })
    const erased = applyErasure(pinned, {
      region: 'r0',
      regions: [],
      nodes: ['a', 'ah'],
      wires: ['ahead'],
    })
    expect(erased.nodes.a).toBeUndefined()
    expect(derivedScope(erased, 'x')).toBe('r0')
    // hold and p are x's two ends; the cap was a no-op.
    expect(erased.wires.x!.endpoints.map((ep) => ep.node).sort()).toEqual(['hold', 'p'])
  })

  it('pins a wire that loses every local incidence, even when supported elsewhere', () => {
    // y reaches B and C at the sheet and one atom two cuts deep. Erasing
    // that atom leaves y's scope and floor globally intact — but the
    // residue rule still caps it at the removal region (Lean clause (a)):
    // the rule's output is a function of the removal site alone, and the
    // pin's region path is a prefix of the removed mention's, so the
    // derived scope cannot move.
    const d = mkDiagram({
      root: 'r0',
      regions: {
        r0: { kind: 'sheet' },
        cut1: { kind: 'cut', parent: 'r0' },
        cut2: { kind: 'cut', parent: 'cut1' },
      },
      nodes: {
        b: { kind: 'atom', region: 'r0', sig: P },
        c: { kind: 'atom', region: 'r0', sig: P },
        q: { kind: 'atom', region: 'cut2', sig: P },
        bh: { kind: 'identity', region: 'r0', sig: P, arity: 1 },
        ch: { kind: 'identity', region: 'r0', sig: P, arity: 1 },
        qh: { kind: 'identity', region: 'cut2', sig: P, arity: 1 },
      },
      wires: {
        y: {
          sig: IOTA,
          endpoints: [
            { node: 'b', port: { kind: 'arg', index: 0 } },
            { node: 'c', port: { kind: 'arg', index: 0 } },
            { node: 'q', port: { kind: 'arg', index: 0 } },
          ],
        },
        bhead: {
          sig: P,
          endpoints: [
            { node: 'b', port: { kind: 'head' } },
            { node: 'bh', port: { kind: 'identity', index: 0 } },
          ],
        },
        chead: {
          sig: P,
          endpoints: [
            { node: 'c', port: { kind: 'head' } },
            { node: 'ch', port: { kind: 'identity', index: 0 } },
          ],
        },
        qhead: {
          sig: P,
          endpoints: [
            { node: 'q', port: { kind: 'head' } },
            { node: 'qh', port: { kind: 'identity', index: 0 } },
          ],
        },
      },
    })
    const erased = applyErasure(d, {
      region: 'cut2',
      regions: [],
      nodes: ['q', 'qh'],
      wires: ['qhead'],
    })
    expect(erased.nodes.q).toBeUndefined()
    expect(derivedScope(erased, 'y')).toBe('r0')
    const yEnds = erased.wires.y!.endpoints.map((ep) => ep.node).sort()
    expect(yEnds).toHaveLength(3)
    expect(yEnds).toContain('b')
    expect(yEnds).toContain('c')
    const capNode = yEnds.find((node) => node !== 'b' && node !== 'c')!
    expect(erased.nodes[capNode]).toMatchObject({
      kind: 'identity',
      region: 'cut2',
      arity: 1,
    })
  })
})

describe('deiteration caps touched wires', () => {
  /** ¬[P(x)] twice — a justifier cut at the sheet and an iso copy inside
      another cut — where x's only mentions are one in each copy. */
  function twoCopiesFixture(): Diagram {
    return mkDiagram({
      root: 'r0',
      regions: {
        r0: { kind: 'sheet' },
        cutJ: { kind: 'cut', parent: 'r0' },
        cutOuter: { kind: 'cut', parent: 'r0' },
        cutC: { kind: 'cut', parent: 'cutOuter' },
      },
      nodes: {
        pJ: { kind: 'atom', region: 'cutJ', sig: P },
        hJ: { kind: 'identity', region: 'cutJ', sig: P, arity: 1 },
        pC: { kind: 'atom', region: 'cutC', sig: P },
        hC: { kind: 'identity', region: 'cutC', sig: P, arity: 1 },
      },
      wires: {
        x: {
          sig: IOTA,
          endpoints: [
            { node: 'pJ', port: { kind: 'arg', index: 0 } },
            { node: 'pC', port: { kind: 'arg', index: 0 } },
          ],
        },
        hJw: {
          sig: P,
          endpoints: [
            { node: 'pJ', port: { kind: 'head' } },
            { node: 'hJ', port: { kind: 'identity', index: 0 } },
          ],
        },
        hCw: {
          sig: P,
          endpoints: [
            { node: 'pC', port: { kind: 'head' } },
            { node: 'hC', port: { kind: 'identity', index: 0 } },
          ],
        },
      },
    })
  }

  it('removing the copy caps the shared wire at its old scope', () => {
    const d = twoCopiesFixture()
    // x reads at the sheet only through BOTH copies together (DCA of the
    // two cut mentions). Removing the inner copy bare would sink x's
    // quantifier into the justifier cut — the cap keeps it at the sheet.
    expect(derivedScope(d, 'x')).toBe('r0')
    const selection = { region: 'cutOuter', regions: ['cutC'], nodes: [], wires: [] }
    const evidence = findDeiterationEvidence(d, selection)
    const removed = applyDeiteration(d, selection, evidence.justifier, evidence.certificate)
    expect(removed.nodes.pC).toBeUndefined()
    expect(removed.wires.hCw).toBeUndefined()
    expect(derivedScope(removed, 'x')).toBe('r0')
    // The cap lands AT THE REMOVAL REGION (the copy's home, cutOuter) —
    // its path is a prefix of the removed mention's path, so the derived
    // scope is unchanged: DCA(cutJ, cutOuter) = r0.
    const cap = removed.wires.x!.endpoints.find((ep) => {
      const node = removed.nodes[ep.node]!
      return node.kind === 'identity' && node.arity === 1 && node.region === 'cutOuter'
    })
    expect(cap, 'a fresh pin at the removal region stands in for the copy').toBeDefined()
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
      kind: 'pin', wire: 'x', node: 'hold', region: outer,
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
      kind: 'pin', wire: 'arg', node: 'hold', region: 'cut',
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
