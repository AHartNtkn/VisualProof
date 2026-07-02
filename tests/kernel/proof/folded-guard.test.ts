import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { termEq } from '../../../src/kernel/term/term'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import type { DiagramNode } from '../../../src/kernel/diagram/diagram'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { boundaryFingerprint } from '../../../src/kernel/diagram/canonical/fingerprint'
import { applyStep } from '../../../src/kernel/proof/step'
import type { ProofContext, ProofStep } from '../../../src/kernel/proof/step'
import { checkTheorem } from '../../../src/kernel/proof/theorem'
import type { Theorem } from '../../../src/kernel/proof/theorem'
import { applyRelUnfold } from '../../../src/kernel/rules/reldef'

/**
 * The exact usage pattern the arithmetic theorems will follow: a theorem whose
 * statement ships with a FOLDED relation guard on a boundary line, whose
 * derivation unfolds only a WORKING COPY of that guard, and whose stated rhs
 * keeps the ambient guard folded. This proves fold survives a derivation and
 * that folded/unfolded statements are DISTINCT statements (ref-keyed identity).
 */

const p = (s: string) => parseTerm(s)

/** R(x): a two-node closed body — the argument line `x` plus a disconnected
 *  closed-term conjunct (a clean node for the derivation to operate on). */
function bodyR() {
  const b = new DiagramBuilder()
  const tArg = b.termNode(b.root, p('y')) // freeVar y is the argument line
  b.termNode(b.root, p('\\z. z')) // a disconnected closed conjunct
  const bound = b.wire(b.root, [{ node: tArg, port: { kind: 'freeVar', name: 'y' } }])
  return mkDiagramWithBoundary(b.build(), [bound])
}

const isConjunct = (n: DiagramNode): boolean => n.kind === 'term' && termEq(n.term, p('\\z. z'))

describe('folded-guard integration proof', () => {
  it('unfolds a working copy while the ambient guard stays folded, and folded ≠ unfolded statements', () => {
    const relations = new Map([['R', bodyR()]])
    const ctx: ProofContext = { theorems: new Map(), relations }

    // lhs: a single folded reference R(x) with x as the boundary line.
    const lb = new DiagramBuilder()
    const ref = lb.ref(lb.root, 'R', 1)
    const x = lb.wire(lb.root, [{ node: ref, port: { kind: 'arg', index: 0 } }])
    const lhs = mkDiagramWithBoundary(lb.build(), [x])

    // Build the derivation by executing it (fresh ids are deterministic, so the
    // recorded concrete-id steps replay identically inside checkTheorem).
    const steps: ProofStep[] = []
    let cur = lhs.diagram

    // 1. iterate the guard into a working sibling copy (same region)
    const iterSel = mkSelection(cur, { region: cur.root, regions: [], nodes: [ref], wires: [] })
    const s1: ProofStep = { rule: 'iteration', sel: iterSel, target: cur.root }
    cur = applyStep(cur, s1, ctx); steps.push(s1)
    expect(Object.values(cur.nodes).filter((n) => n.kind === 'ref')).toHaveLength(2)

    // 2. unfold the COPY only (the ref that is not the original)
    const copyId = Object.entries(cur.nodes).find(([id, n]) => n.kind === 'ref' && id !== ref)![0]
    const s2: ProofStep = { rule: 'relUnfold', node: copyId }
    cur = applyStep(cur, s2, ctx); steps.push(s2)
    expect(Object.values(cur.nodes).filter((n) => n.kind === 'ref')).toHaveLength(1) // ambient survives

    // 3. one real rule application inside the unfolded material: double-cut the conjunct
    const qNode = Object.entries(cur.nodes).find(([, n]) => isConjunct(n))![0]
    const wrapSel = mkSelection(cur, { region: cur.root, regions: [], nodes: [qNode], wires: [] })
    const s3: ProofStep = { rule: 'doubleCutIntro', sel: wrapSel }
    cur = applyStep(cur, s3, ctx); steps.push(s3)

    // rhs keeps the ambient guard folded (the ref is still there)
    const rhs = mkDiagramWithBoundary(cur, lhs.boundary)
    const thm: Theorem = { name: 'foldedGuard', lhs, rhs, steps }

    // (a) the theorem verifies end to end
    expect(() => checkTheorem(thm, ctx)).not.toThrow()

    // (b) the ambient fold survived the derivation
    const refsInRhs = Object.values(rhs.diagram.nodes).filter((n) => n.kind === 'ref')
    expect(refsInRhs).toHaveLength(1)

    // (c) statement identity is ref-keyed: unfolding the ambient guard too yields a
    //     diagram that is NOT isomorphic to the actual (folded) rhs — folded and
    //     unfolded statements are distinct statements.
    const ambientRef = Object.entries(rhs.diagram.nodes).find(([, n]) => n.kind === 'ref')![0]
    const unfoldEverything = applyRelUnfold(rhs.diagram, ambientRef, relations)
    expect(boundaryFingerprint(mkDiagramWithBoundary(unfoldEverything, lhs.boundary)))
      .not.toBe(boundaryFingerprint(rhs))
    // and the unfold-everything variant carries NO ref at all
    expect(Object.values(unfoldEverything.nodes).some((n) => n.kind === 'ref')).toBe(false)
  })
})
