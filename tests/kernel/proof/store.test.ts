import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
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

  it('rejects unversioned or alien envelopes', () => {
    expect(() => loadTheory({ format: 'something-else', version: 1, definitions: {}, relations: {}, theorems: [] }))
      .toThrowError(/format/)
    expect(() => loadTheory({ format: 'visual-proof-theory', version: 99, definitions: {}, relations: {}, theorems: [] }))
      .toThrowError(/version/)
  })
})
