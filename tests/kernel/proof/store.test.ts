import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { freePorts } from '../../../src/kernel/term/term'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import type { Theorem } from '../../../src/kernel/proof/theorem'
import type { Theory } from '../../../src/kernel/proof/store'
import { verifyTheory, theoryToJson, loadTheory } from '../../../src/kernel/proof/store'
import { ProofError } from '../../../src/kernel/proof/error'
import { singleStepAction } from '../../../src/kernel/proof/action'

const p = (s: string) => parseTerm(s)

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
    actions: [singleStepAction('drop Q', { rule: 'erasure', sel: { region: lhs.diagram.root, regions: [], nodes: [lq], wires: [] } })],
  }
}

function isIdentity() {
  const b = new DiagramBuilder()
  const n = b.termNode(b.root, p('\\x. x'))
  const w = b.wire(b.root, [{ node: n, port: { kind: 'output' } }])
  return mkDiagramWithBoundary(b.build(), [w])
}

function groupedNoop(): Theorem {
  const b = new DiagramBuilder()
  const side = mkDiagramWithBoundary(b.build(), [])
  return {
    name: 'groupedNoop',
    lhs: side,
    rhs: side,
    actions: [{
      label: 'introduce and eliminate a double cut',
      steps: [
        { rule: 'doubleCutIntro', sel: { region: side.diagram.root, regions: [], nodes: [], wires: [] } },
        { rule: 'doubleCutElim', region: 'dc' },
      ],
      placements: [],
    }],
  }
}

describe('verifyTheory', () => {
  it('verifies relations, theorems in order and returns the context', () => {
    const theory: Theory = {
      relations: { isIdentity: isIdentity() },
      theorems: [dropQ()],
    }
    const ctx = verifyTheory(theory)
    expect(ctx.theorems.has('dropQ')).toBe(true)
  })

  it('rejects duplicate theorem names and broken proofs, by name', () => {
    const t = dropQ()
    expect(() => verifyTheory({ relations: {}, theorems: [t, t] }))
      .toThrowError(/duplicate theorem name 'dropQ'/)
    const broken: Theorem = { ...t, actions: [] }
    let caught: unknown
    try { verifyTheory({ relations: {}, theorems: [broken] }) } catch (e) { caught = e }
    expect(caught).toBeInstanceOf(ProofError)
  })

  it('later theorems may use earlier ones, not vice versa', () => {
    const base = dropQ()
    // derived: applies dropQ inside its own proof
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
    const derived: Theorem = {
      name: 'viaDropQ', lhs, rhs,
      actions: [singleStepAction('cite drop Q', {
        rule: 'theorem', name: 'dropQ',
        at: { sel: { region: lhs.diagram.root, regions: [], nodes: [lp, lq], wires: [] }, args: [lb] },
        direction: 'forward',
      })],
    }
    expect(() => verifyTheory({ relations: {}, theorems: [base, derived] })).not.toThrow()
    expect(() => verifyTheory({ relations: {}, theorems: [derived, base] }))
      .toThrowError(/unknown theorem 'dropQ'/)
  })
})

describe('verifyTheory — relation references', () => {
  /** A self-contained arity-1 body: a term node whose free var is the argument. */
  function simpleBody() {
    const b = new DiagramBuilder()
    const t = b.termNode(b.root, p('y'))
    const w = b.wire(b.root, [{ node: t, port: { kind: 'freeVar', name: 'y' } }])
    return mkDiagramWithBoundary(b.build(), [w])
  }

  /** A theorem whose (identical) sides are a single reference node. */
  function refTheorem(defId: string, arity = 1): Theorem {
    const b = new DiagramBuilder()
    const node = b.ref(b.root, defId, arity)
    const w = b.wire(b.root, [{ node, port: { kind: 'arg', index: 0 } }])
    const side = mkDiagramWithBoundary(b.build(), [w])
    return { name: 'refThm', lhs: side, rhs: side, actions: [] }
  }

  it('verifies a theory whose theorem references a declared relation, exposing it in ctx', () => {
    const ctx = verifyTheory({ relations: { R: simpleBody() }, theorems: [refTheorem('R')] })
    expect(ctx.relations.has('R')).toBe(true)
    expect(ctx.relations.get('R')!.boundary).toHaveLength(1)
  })

  it('accepts a relation body with a top-level bubble (∃S[S(x)]-shaped, closed by construction)', () => {
    // A bubble directly under the body root is a legitimate ∃-quantifier, not an
    // "external binder": a stored body is closed, and relUnfold copies the bubble
    // as fresh content. Verification must accept it, and it round-trips through
    // theoryToJson/loadTheory unchanged.
    const b = new DiagramBuilder()
    const bub = b.bubble(b.root, 1)
    const at = b.atom(bub, bub)
    const bound = b.wire(b.root, [{ node: at, port: { kind: 'arg', index: 0 } }])
    const existsBody = mkDiagramWithBoundary(b.build(), [bound])
    expect(() => verifyTheory({ relations: { R: existsBody }, theorems: [] })).not.toThrow()
    const json = theoryToJson({ relations: { R: existsBody }, theorems: [] })
    const { ctx } = loadTheory(JSON.parse(JSON.stringify(json)))
    expect(ctx.relations.has('R')).toBe(true)
  })

  it('verifies and reloads a relation whose two boundary positions share one identity', () => {
    const b = new DiagramBuilder()
    const node = b.termNode(b.root, p('y'))
    const shared = b.wire(b.root, [{ node, port: { kind: 'output' } }])
    const alias = mkDiagramWithBoundary(b.build(), [shared, shared])
    const json = theoryToJson({ relations: { Alias: alias }, theorems: [] })
    const { ctx } = loadTheory(JSON.parse(JSON.stringify(json)))
    expect(ctx.relations.get('Alias')?.boundary).toEqual([shared, shared])
  })

  it('refuses a theorem side whose reference names an unknown relation', () => {
    expect(() => verifyTheory({ relations: {}, theorems: [refTheorem('ghost')] }))
      .toThrowError(/left-hand side: reference node .* names unknown relation 'ghost'/)
  })

  it('refuses a theorem side whose reference arity disagrees with the relation', () => {
    expect(() => verifyTheory({ relations: { R: simpleBody() }, theorems: [refTheorem('R', 2)] }))
      .toThrowError(/has arity 2 but the relation has arity 1/)
  })
})

describe('check-before-register invariant', () => {
  it('a theorem whose proof cites its own name is refused (no self-citation)', () => {
    // If register came before check, 'selfCite' would be in the context when
    // its own proof is replayed, enabling circular justification.
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
    const selfCite: Theorem = {
      name: 'selfCite', lhs, rhs,
      actions: [singleStepAction('self cite', {
        rule: 'theorem', name: 'selfCite',
        at: { sel: { region: lhs.diagram.root, regions: [], nodes: [lp, lq], wires: [] }, args: [lb] },
        direction: 'forward',
      })],
    }
    expect(() => verifyTheory({ relations: {}, theorems: [selfCite] }))
      .toThrowError(/unknown theorem 'selfCite'/)
  })
})

describe('theory files', () => {
  it('round-trips through JSON with verification on load', () => {
    const theory: Theory = {
      relations: { isIdentity: isIdentity() },
      theorems: [dropQ(), groupedNoop()],
    }
    const text = JSON.stringify(theoryToJson(theory))
    const { theory: back, ctx } = loadTheory(JSON.parse(text))
    expect(ctx.theorems.has('dropQ')).toBe(true)
    expect(back.theorems[1]!.actions).toEqual(theory.theorems[1]!.actions)
    expect(JSON.stringify(theoryToJson(back))).toBe(text)
  })

  it('canonicalizes stored non-canonical free-port names on load rather than trusting them', () => {
    // A hand-crafted file carrying ORIGINAL names (v:y, v:z): the load path
    // runs through mkDiagram, so the diagram that comes out spells s0, s1 in
    // both the node term and the wire endpoints — files are data, the kernel
    // re-establishes its own invariants.
    const j = {
      format: 'visual-proof-theory',
      version: 1,
      relations: {
        R: {
          diagram: {
            root: 'r0',
            regions: { r0: { kind: 'sheet' } },
            nodes: { n0: { kind: 'term', region: 'r0', term: 'A(P("y"),P("z"))' } },
            wires: {
              w0: { scope: 'r0', endpoints: [{ node: 'n0', port: 'out' }] },
              w1: { scope: 'r0', endpoints: [{ node: 'n0', port: 'v:y' }] },
              w2: { scope: 'r0', endpoints: [{ node: 'n0', port: 'v:z' }] },
            },
          },
          boundary: ['w1', 'w2'],
        },
      },
      theorems: [],
    }
    const { theory } = loadTheory(j)
    const d = theory.relations['R']!.diagram
    const n = d.nodes['n0']
    expect(n?.kind === 'term' && freePorts(n.term)).toEqual(['s0', 's1'])
    expect(d.wires['w1']?.endpoints).toEqual([{ node: 'n0', port: { kind: 'freeVar', name: 's0' } }])
    expect(d.wires['w2']?.endpoints).toEqual([{ node: 'n0', port: { kind: 'freeVar', name: 's1' } }])
  })

  it('rejects unversioned or alien envelopes', () => {
    expect(() => loadTheory({ format: 'something-else', version: 1, relations: {}, theorems: [] }))
      .toThrowError(/format/)
    expect(() => loadTheory({ format: 'visual-proof-theory', version: 99, relations: {}, theorems: [] }))
      .toThrowError(/version/)
  })
})
