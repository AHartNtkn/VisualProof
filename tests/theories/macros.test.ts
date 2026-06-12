import { describe, it, expect } from 'vitest'
import { DerivationCursor, extractClosedPattern } from '../../src/theories/macros'
import { parseTerm } from '../../src/kernel/term/parse'
import { termEq } from '../../src/kernel/term/term'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import type { ProofContext } from '../../src/kernel/proof/step'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)
const ctx: ProofContext = { definitions: {}, theorems: new Map() }

describe('DerivationCursor', () => {
  it('tracks the diagram across pushes: a doubleCutIntro gains two regions', () => {
    const b = new DiagramBuilder()
    const d = b.build()
    const c = new DerivationCursor(d, ctx)
    c.push('wrap', {
      rule: 'doubleCutIntro',
      sel: mkSelection(c.cur, { region: c.cur.root, regions: [], nodes: [], wires: [] }),
    })
    expect(Object.keys(c.cur.regions)).toHaveLength(Object.keys(d.regions).length + 2)
    expect(c.steps).toHaveLength(1)
  })

  it('a failing step throws with the step named and leaves the cursor untouched', () => {
    const b = new DiagramBuilder()
    const d = b.build()
    const c = new DerivationCursor(d, ctx)
    expect(() => c.push('bogus unwrap', { rule: 'doubleCutElim', region: d.root })).toThrowError(
      /bogus unwrap/,
    )
    expect(c.steps).toHaveLength(0)
    expect(c.cur).toBe(d)
  })
})

describe('kMat', () => {
  it('materializes a closed term node at root on a fresh singleton wire', () => {
    const b = new DiagramBuilder()
    const seed = b.termNode(b.root, p('\\x. x'))
    b.wire(b.root, [{ node: seed, port: { kind: 'output' } }])
    const d = b.build()
    const c = new DerivationCursor(d, ctx)
    const s = p('\\x. \\y. x')
    const made = c.kMat('mat', seed, s, {})
    const n = c.cur.nodes[made]!
    expect(n.kind === 'term' && n.region === c.cur.root && termEq(n.term, s)).toBe(true)
    // the seed is restored to its original term
    expect(termEq(c.termOf(seed), p('\\x. x'))).toBe(true)
    // the output rides a FRESH wire holding only the made node's output
    const w = c.wireOf(made, 'output')
    expect(d.wires[w]).toBeUndefined()
    expect(c.cur.wires[w]!.endpoints).toEqual([{ node: made, port: { kind: 'output' } }])
    // expand + fission + restore
    expect(c.steps).toHaveLength(3)
  })

  it('materializes inside a cut (negative region) — no polarity gate', () => {
    const b = new DiagramBuilder()
    const cut = b.cut(b.root)
    const seed = b.termNode(cut, p('\\x. x'))
    b.wire(cut, [{ node: seed, port: { kind: 'output' } }])
    const d = b.build()
    const c = new DerivationCursor(d, ctx)
    const s = p('\\x. \\y. y')
    const made = c.kMat('matNeg', seed, s, {})
    const n = c.cur.nodes[made]!
    expect(n.kind === 'term' && n.region === cut && termEq(n.term, s)).toBe(true)
    const w = c.wireOf(made, 'output')
    expect(c.cur.wires[w]!.scope).toBe(cut)
    expect(c.cur.wires[w]!.endpoints).toHaveLength(1)
  })

  it('attaches a free port of the materialized term to a caller-named existing wire', () => {
    const b = new DiagramBuilder()
    const seed = b.termNode(b.root, p('\\x. x'))
    b.wire(b.root, [{ node: seed, port: { kind: 'output' } }])
    const host = b.termNode(b.root, p('\\x. x q'))
    const wq = b.wire(b.root, [{ node: host, port: { kind: 'freeVar', name: 'q' } }])
    const d = b.build()
    const c = new DerivationCursor(d, ctx)
    const s = p('\\x. q')
    const made = c.kMat('matFree', seed, s, { q: wq })
    expect(termEq(c.termOf(made), s)).toBe(true)
    // the made node's q endpoint landed on the NAMED wire, joining the host's
    expect(c.wireOf(made, 'freeVar', 'q')).toBe(wq)
    expect(c.cur.wires[wq]!.endpoints).toHaveLength(2)
    // its output still rides a fresh singleton wire
    const w = c.wireOf(made, 'output')
    expect(d.wires[w]).toBeUndefined()
    expect(c.cur.wires[w]!.endpoints).toHaveLength(1)
    // the seed carries no residue of the trick
    expect(termEq(c.termOf(seed), p('\\x. x'))).toBe(true)
  })
})

describe('extractClosedPattern', () => {
  it('lifts a derived cut into a pattern that inserts with empty attachments', () => {
    const b = new DiagramBuilder()
    const cut = b.cut(b.root)
    const n = b.termNode(cut, p('\\x. x'))
    b.wire(cut, [{ node: n, port: { kind: 'output' } }])
    const d = b.build()
    const pat = extractClosedPattern(d, { region: d.root, regions: [cut], nodes: [], wires: [] })
    expect(pat.boundary).toHaveLength(0)

    // usable as-is: insert into a negative region of another diagram
    const hb = new DiagramBuilder()
    const hcut = hb.cut(hb.root)
    const c = new DerivationCursor(hb.build(), ctx)
    c.push('insert fact', { rule: 'insertion', region: hcut, pattern: pat, attachments: [], binders: {} })
    const copies = Object.entries(c.cur.regions).filter(
      ([, r]) => r.kind === 'cut' && r.parent === hcut,
    )
    expect(copies).toHaveLength(1)
    const copied = Object.values(c.cur.nodes).filter(
      (x) => x.kind === 'term' && x.region === copies[0]![0],
    )
    expect(copied).toHaveLength(1)
  })

  it('rejects an open extraction: a touching wire needs attachments downstream', () => {
    const b = new DiagramBuilder()
    const cut = b.cut(b.root)
    const n = b.termNode(cut, p('\\x. x q'))
    b.wire(cut, [{ node: n, port: { kind: 'output' } }])
    b.wire(b.root, [{ node: n, port: { kind: 'freeVar', name: 'q' } }])
    const d = b.build()
    expect(() =>
      extractClosedPattern(d, { region: d.root, regions: [cut], nodes: [], wires: [] }),
    ).toThrowError(/open/)
  })
})
