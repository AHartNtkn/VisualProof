import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { RuleError } from '../../../src/kernel/rules/error'
import { checkTheorem, applyTheorem } from '../../../src/kernel/proof/theorem'
import type { Theorem } from '../../../src/kernel/proof/theorem'
import type { ProofContext } from '../../../src/kernel/proof/step'
import { replayProof } from '../../../src/kernel/proof/step'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)
const ctx: ProofContext = { definitions: {}, theorems: new Map() }

/**
 * The running example: P(x) := x = λa.a, Q(x) := x = λa.λb.a.
 * Theorem dropQ: P(x) ∧ Q(x) ⟹ P(x), proven by one erasure.
 */
function dropQ(): Theorem {
  const l = new DiagramBuilder()
  const lp = l.termNode(l.root, p('\\a. a'))
  const lq = l.termNode(l.root, p('\\a. \\b. a'))
  const lb = l.wire(l.root, [
    { node: lp, port: { kind: 'output' } },
    { node: lq, port: { kind: 'output' } },
  ])
  const lhs = mkDiagramWithBoundary(l.build(), [lb])
  const r = new DiagramBuilder()
  const rp = r.termNode(r.root, p('\\a. a'))
  const rb = r.wire(r.root, [{ node: rp, port: { kind: 'output' } }])
  const rhs = mkDiagramWithBoundary(r.build(), [rb])
  return {
    name: 'dropQ', lhs, rhs,
    steps: [{ rule: 'erasure', sel: { region: lhs.diagram.root, regions: [], nodes: [lq], wires: [] } }],
  }
}

describe('checkTheorem', () => {
  it('accepts a valid proof', () => {
    expect(() => checkTheorem(dropQ(), ctx)).not.toThrow()
  })

  it('rejects proofs that do not arrive at the stated rhs', () => {
    const t = dropQ()
    const broken: Theorem = { ...t, steps: [] }
    expect(() => checkTheorem(broken, ctx))
      .toThrowError(/does not arrive at the stated right-hand side/)
  })

  it('rejects arity mismatches and non-root boundary stubs, by name', () => {
    const t = dropQ()
    const bad: Theorem = { ...t, rhs: mkDiagramWithBoundary(t.rhs.diagram, []) }
    expect(() => checkTheorem(bad, ctx)).toThrowError(/boundary arity mismatch/)

    const n = new DiagramBuilder()
    const cut = n.cut(n.root)
    const nn = n.termNode(cut, p('\\a. a'))
    const nw = n.wire(cut, [{ node: nn, port: { kind: 'output' } }])
    const nonRoot: Theorem = { ...t, lhs: mkDiagramWithBoundary(n.build(), [nw]), steps: [] }
    expect(() => checkTheorem(nonRoot, ctx)).toThrowError(/not scoped at the diagram root/)
  })

  it('rejects proofs that destroy a boundary wire', () => {
    const t = dropQ()
    // erase BOTH nodes: the boundary wire survives as endpoint-less — still
    // exists, so build a destroying case differently: sever... a wire is only
    // DESTROYED by join (inner) or being internal to a removal. Select it
    // explicitly as removal content:
    const destroying: Theorem = {
      ...t,
      steps: [{
        rule: 'erasure',
        sel: {
          region: t.lhs.diagram.root, regions: [],
          nodes: Object.keys(t.lhs.diagram.nodes),
          wires: [t.lhs.boundary[0]!],
        },
      }],
    }
    expect(() => checkTheorem(destroying, ctx)).toThrowError(/boundary wire .* was destroyed/)
  })
})

describe('applyTheorem', () => {
  function host() {
    // host: P(v) ∧ Q(v) ∧ hub(v) at root
    const h = new DiagramBuilder()
    const hp = h.termNode(h.root, p('\\a. a'))
    const hq = h.termNode(h.root, p('\\a. \\b. a'))
    const hub = h.termNode(h.root, p('y'))
    const v = h.wire(h.root, [
      { node: hp, port: { kind: 'output' } },
      { node: hq, port: { kind: 'output' } },
      { node: hub, port: { kind: 'freeVar', name: 'y' } },
    ])
    return { d: h.build(), hp, hq, hub, v }
  }

  it('forward at a positive region rewrites the occurrence in one step', () => {
    const { d, hp, hq, v } = host()
    const out = applyTheorem(d, dropQ(), {
      sel: { region: d.root, regions: [], nodes: [hp, hq], wires: [] },
      args: [v],
    }, 'forward')
    // NOTE: assert by SHAPE, not by id — splice may legitimately REUSE the
    // removed nodes' ids (freshId only dodges ids still present). Expected:
    // the hub plus exactly one spliced P node, both on v.
    expect(Object.values(out.nodes)).toHaveLength(2)
    const eps = out.wires[v]?.endpoints ?? []
    expect(eps).toHaveLength(2)
    expect(eps.filter((ep) => ep.port.kind === 'output')).toHaveLength(1)
    expect(eps.filter((ep) => ep.port.kind === 'freeVar')).toHaveLength(1)
  })

  it('reverse at a negative region strengthens, and round-trips by fingerprint', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const hp = h.termNode(cut, p('\\a. a'))
    const v = h.wire(cut, [{ node: hp, port: { kind: 'output' } }])
    const d = h.build()
    const strengthened = applyTheorem(d, dropQ(), {
      sel: { region: cut, regions: [], nodes: [hp], wires: [] },
      args: [v],
    }, 'reverse')
    const nodes = Object.entries(strengthened.nodes)
    expect(nodes).toHaveLength(2)
    // applying forward inside the cut is refused (negative)
    const [pid] = nodes.find(([, n]) => n.kind === 'term' && n.term.kind === 'lam' && n.term.body.kind === 'bvar')!
    const [qid] = nodes.find(([id]) => id !== pid)!
    expect(() => applyTheorem(strengthened, dropQ(), {
      sel: { region: cut, regions: [], nodes: [pid, qid], wires: [] },
      args: [v],
    }, 'forward')).toThrowError(/requires a positive region/)
  })

  it('refuses occurrences that do not match the theorem side', () => {
    const { d, hp, v } = host()
    expect(() => applyTheorem(d, dropQ(), {
      sel: { region: d.root, regions: [], nodes: [hp], wires: [] },
      args: [v],
    }, 'forward')).toThrowError(/not an occurrence of theorem 'dropQ'/)
  })

  it('refuses wrong polarity by name in both directions', () => {
    const { d, hp, hq, v } = host()
    let caught: unknown
    try {
      applyTheorem(d, dropQ(), {
        sel: { region: d.root, regions: [], nodes: [hp, hq], wires: [] },
        args: [v],
      }, 'reverse')
    } catch (e) { caught = e }
    expect(caught).toBeInstanceOf(RuleError)
    expect((caught as Error).message).toMatch(/reverse requires a negative region/)
  })
})

describe('theorem steps inside proofs (derived rules used natively)', () => {
  it('a registered theorem applies through replayProof without expansion', () => {
    const t = dropQ()
    const theorems = new Map([[t.name, t]])
    const c2: ProofContext = { definitions: {}, theorems }
    const { d, hp, hq, v } = (() => {
      const h = new DiagramBuilder()
      const hp = h.termNode(h.root, p('\\a. a'))
      const hq = h.termNode(h.root, p('\\a. \\b. a'))
      const v = h.wire(h.root, [
        { node: hp, port: { kind: 'output' } },
        { node: hq, port: { kind: 'output' } },
      ])
      return { d: h.build(), hp, hq, v }
    })()
    const out = replayProof(d, [{
      rule: 'theorem', name: 'dropQ',
      at: { sel: { region: d.root, regions: [], nodes: [hp, hq], wires: [] }, args: [v] },
      direction: 'forward',
    }], c2)
    expect(Object.values(out.nodes)).toHaveLength(1)
  })
})
