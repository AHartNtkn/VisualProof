import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { freePorts } from '../../../src/kernel/term/term'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import type { Theorem } from '../../../src/kernel/proof/theorem'
import type { Theory } from '../../../src/kernel/proof/store'
import { verifyTheory, theoryToJson, loadTheory } from '../../../src/kernel/proof/store'
import { ProofError } from '../../../src/kernel/proof/error'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

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

function isIdentity() {
  const b = new DiagramBuilder()
  const n = b.termNode(b.root, p('\\x. x'))
  const w = b.wire(b.root, [{ node: n, port: { kind: 'output' } }])
  return mkDiagramWithBoundary(b.build(), [w])
}

describe('verifyTheory', () => {
  it('verifies definitions, relations, theorems in order and returns the context', () => {
    const theory: Theory = {
      definitions: { I: p('\\x. x') },
      relations: { isIdentity: isIdentity() },
      theorems: [dropQ()],
    }
    const ctx = verifyTheory(theory)
    expect(ctx.theorems.has('dropQ')).toBe(true)
  })

  it('rejects duplicate theorem names and broken proofs, by name', () => {
    const t = dropQ()
    expect(() => verifyTheory({ definitions: {}, relations: {}, theorems: [t, t] }))
      .toThrowError(/duplicate theorem name 'dropQ'/)
    const broken: Theorem = { ...t, steps: [] }
    let caught: unknown
    try { verifyTheory({ definitions: {}, relations: {}, theorems: [broken] }) } catch (e) { caught = e }
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
      steps: [{
        rule: 'theorem', name: 'dropQ',
        at: { sel: { region: lhs.diagram.root, regions: [], nodes: [lp, lq], wires: [] }, args: [lb] },
        direction: 'forward',
      }],
    }
    expect(() => verifyTheory({ definitions: {}, relations: {}, theorems: [base, derived] })).not.toThrow()
    expect(() => verifyTheory({ definitions: {}, relations: {}, theorems: [derived, base] }))
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
    return { name: 'refThm', lhs: side, rhs: side, steps: [] }
  }

  it('verifies a theory whose theorem references a declared relation, exposing it in ctx', () => {
    const ctx = verifyTheory({ definitions: {}, relations: { R: simpleBody() }, theorems: [refTheorem('R')] })
    expect(ctx.relations.has('R')).toBe(true)
    expect(ctx.relations.get('R')!.boundary).toHaveLength(1)
  })

  it('refuses a relation body carrying an external binder stub (top-level binder)', () => {
    // A bubble directly under the body root is the extractSubgraph open-pattern
    // representation — deferred, so verification must refuse it.
    const b = new DiagramBuilder()
    const bub = b.bubble(b.root, 1)
    const at = b.atom(bub, bub)
    const bound = b.wire(b.root, [{ node: at, port: { kind: 'arg', index: 0 } }])
    const openBody = mkDiagramWithBoundary(b.build(), [bound])
    expect(() => verifyTheory({ definitions: {}, relations: { R: openBody }, theorems: [] }))
      .toThrowError(/relation 'R': body has an external binder stub/)
  })

  it('refuses a theorem side whose reference names an unknown relation', () => {
    expect(() => verifyTheory({ definitions: {}, relations: {}, theorems: [refTheorem('ghost')] }))
      .toThrowError(/left-hand side: reference node .* names unknown relation 'ghost'/)
  })

  it('refuses a theorem side whose reference arity disagrees with the relation', () => {
    expect(() => verifyTheory({ definitions: {}, relations: { R: simpleBody() }, theorems: [refTheorem('R', 2)] }))
      .toThrowError(/has arity 2 but the relation has arity 1/)
  })

  it('loadTheory rejects a file whose relation body carries an external binder stub', () => {
    const b = new DiagramBuilder()
    const bub = b.bubble(b.root, 1)
    const at = b.atom(bub, bub)
    const bound = b.wire(b.root, [{ node: at, port: { kind: 'arg', index: 0 } }])
    const openBody = mkDiagramWithBoundary(b.build(), [bound])
    const json = theoryToJson({ definitions: {}, relations: { R: openBody }, theorems: [] })
    expect(() => loadTheory(JSON.parse(JSON.stringify(json))))
      .toThrowError(/relation 'R': body has an external binder stub/)
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
      steps: [{
        rule: 'theorem', name: 'selfCite',
        at: { sel: { region: lhs.diagram.root, regions: [], nodes: [lp, lq], wires: [] }, args: [lb] },
        direction: 'forward',
      }],
    }
    expect(() => verifyTheory({ definitions: {}, relations: {}, theorems: [selfCite] }))
      .toThrowError(/unknown theorem 'selfCite'/)
  })
})

describe('theory files', () => {
  it('round-trips through JSON with verification on load', () => {
    const theory: Theory = {
      definitions: { I: p('\\x. x') },
      relations: { isIdentity: isIdentity() },
      theorems: [dropQ()],
    }
    const text = JSON.stringify(theoryToJson(theory))
    const { theory: back, ctx } = loadTheory(JSON.parse(text))
    expect(ctx.theorems.has('dropQ')).toBe(true)
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
      definitions: {},
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
    expect(() => loadTheory({ format: 'something-else', version: 1, definitions: {}, relations: {}, theorems: [] }))
      .toThrowError(/format/)
    expect(() => loadTheory({ format: 'visual-proof-theory', version: 99, definitions: {}, relations: {}, theorems: [] }))
      .toThrowError(/version/)
  })
})
