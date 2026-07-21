import { describe, it, expect } from 'vitest'
import { DerivationCursor } from '../../src/theories/macros'
import { parseTerm } from '../../src/kernel/term/parse'
import { termEq } from '../../src/kernel/term/term'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { EMPTY_PROOF_CONTEXT, type ProofContext } from '../../src/kernel/proof/context'

const p = (s: string) => parseTerm(s)
const ctx: ProofContext = EMPTY_PROOF_CONTEXT

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
    expect(c.actions).toHaveLength(1)
  })

  it('a failing step throws with the step named and leaves the cursor untouched', () => {
    const b = new DiagramBuilder()
    const d = b.build()
    const c = new DerivationCursor(d, ctx)
    expect(() => c.push('bogus unwrap', { rule: 'doubleCutElim', region: d.root })).toThrowError(
      /bogus unwrap/,
    )
    expect(c.actions).toHaveLength(0)
    expect(c.cur).toBe(d)
  })
})

describe('intro', () => {
  it('introduces a closed term node at root on a fresh singleton wire, one step', () => {
    const b = new DiagramBuilder()
    const bystander = b.termNode(b.root, p('\\x. x'))
    b.wire(b.root, [{ node: bystander, port: { kind: 'output' } }])
    const d = b.build()
    const c = new DerivationCursor(d, ctx)
    const s = p('\\x. \\y. x')
    const made = c.intro('mat', c.cur.root, s)
    const n = c.cur.nodes[made]!
    expect(n.kind === 'term' && n.region === c.cur.root && termEq(n.term, s)).toBe(true)
    // the bystander keeps its original term — no seed trickery touches it
    expect(termEq(c.termOf(bystander), p('\\x. x'))).toBe(true)
    // the output rides a FRESH wire holding only the made node's output
    const w = c.wireOf(made, 'output')
    expect(d.wires[w]).toBeUndefined()
    expect(c.cur.wires[w]!.endpoints).toEqual([{ node: made, port: { kind: 'output' } }])
    // one honest rule application, not expand + fission + restore
    expect(c.actions).toHaveLength(1)
  })

  it('introduces inside a cut (negative region) — no polarity gate, no seed needed', () => {
    const b = new DiagramBuilder()
    const cut = b.cut(b.root)
    const d = b.build()
    const c = new DerivationCursor(d, ctx)
    const s = p('\\x. \\y. y')
    const made = c.intro('matNeg', cut, s)
    const n = c.cur.nodes[made]!
    expect(n.kind === 'term' && n.region === cut && termEq(n.term, s)).toBe(true)
    const w = c.wireOf(made, 'output')
    expect(c.cur.wires[w]!.scope).toBe(cut)
    expect(c.cur.wires[w]!.endpoints).toHaveLength(1)
  })

  it('refuses an open term with the step named and leaves the cursor untouched', () => {
    const b = new DiagramBuilder()
    const host = b.termNode(b.root, p('\\x. x q'))
    b.wire(b.root, [{ node: host, port: { kind: 'freeVar', name: 'q' } }])
    const d = b.build()
    const c = new DerivationCursor(d, ctx)
    expect(() => c.intro('matFree', c.cur.root, p('\\x. q')))
      .toThrowError(/matFree.*closed-term introduction requires a closed term.*'q'/)
    expect(c.actions).toHaveLength(0)
    expect(c.cur).toBe(d)
  })
})
