import { describe, it, expect } from 'vitest'
import type { Diagram, WireId } from '../../../src/kernel/diagram/diagram'
import { buildFregeTheory } from '../../../src/theories/frege'
import { buildLambdaTheory } from '../../../src/theories/lambda'
import { verifyTheory, type Theory } from '../../../src/kernel/proof/store'
import { replayProof } from '../../../src/kernel/proof/step'
import { diagramFingerprint, boundaryFingerprint } from '../../../src/kernel/diagram/canonical/fingerprint'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { exploreForm } from '../../../src/kernel/diagram/canonical/explore'

/**
 * Task 3 spike-proof (relFold's gate is soundness-critical): the new canonical
 * explorer's labeling must induce the SAME equivalence as the old fingerprint
 * across the ENTIRE bundled corpus — every relation body, every theorem side,
 * every replay step of BOTH theories — BEFORE the old fingerprint path is
 * deleted. Any two complete invariants agree as equivalences, so this passing
 * is the empirical confirmation that the new labeling is a correct complete
 * invariant on the real artifacts relFold and dedup rely on.
 */

type Item = { label: string; diagram: Diagram; boundary?: readonly WireId[] }

function collectCorpus(name: string, theory: Theory): Item[] {
  const ctx = verifyTheory(theory)
  const items: Item[] = []
  for (const [rel, body] of Object.entries(theory.relations)) {
    items.push({ label: `${name}:rel:${rel}`, diagram: body.diagram, boundary: body.boundary })
  }
  for (const thm of theory.theorems) {
    items.push({ label: `${name}:thm:${thm.name}:lhs`, diagram: thm.lhs.diagram, boundary: thm.lhs.boundary })
    items.push({ label: `${name}:thm:${thm.name}:rhs`, diagram: thm.rhs.diagram, boundary: thm.rhs.boundary })
    // replay steps: the initial lhs (unpinned) then every post-step diagram
    items.push({ label: `${name}:thm:${thm.name}:step0`, diagram: thm.lhs.diagram })
    replayProof(thm.lhs.diagram, thm.steps, ctx, (d, i) => {
      items.push({ label: `${name}:thm:${thm.name}:step${i + 1}`, diagram: d })
    })
  }
  return items
}

function oldKey(it: Item): string {
  return it.boundary === undefined
    ? diagramFingerprint(it.diagram)
    : boundaryFingerprint(mkDiagramWithBoundary(it.diagram, it.boundary))
}

function newKey(it: Item): string {
  return it.boundary === undefined ? exploreForm(it.diagram) : exploreForm(it.diagram, it.boundary)
}

describe('canonical explorer agrees with the old fingerprint across the bundled corpus', () => {
  const corpus = [
    ...collectCorpus('frege', buildFregeTheory()),
    ...collectCorpus('lambda', buildLambdaTheory()),
  ]

  it('the corpus is non-trivial (both theories, sides, bodies, and replay steps)', () => {
    expect(corpus.length).toBeGreaterThan(40)
    expect(corpus.some((i) => i.boundary !== undefined)).toBe(true)
    expect(corpus.some((i) => i.boundary === undefined)).toBe(true)
  })

  it('new labeling induces the SAME equivalence as the old fingerprint (all pairs)', () => {
    const oldKeys = corpus.map(oldKey)
    const newKeys = corpus.map(newKey)
    let sawEq = false
    let sawNe = false
    for (let i = 0; i < corpus.length; i++) {
      for (let j = i + 1; j < corpus.length; j++) {
        const oldEq = oldKeys[i] === oldKeys[j]
        const newEq = newKeys[i] === newKeys[j]
        expect(
          newEq,
          `disagreement on '${corpus[i]!.label}' vs '${corpus[j]!.label}': old-eq=${oldEq}, new-eq=${newEq}`,
        ).toBe(oldEq)
        if (oldEq) sawEq = true
        else sawNe = true
      }
    }
    // the corpus exercises agreement in both directions
    expect(sawNe).toBe(true)
    expect(sawEq).toBe(true)
  })

  it('boundary-order sensitivity agrees too (reversed pins on multi-arg bodies)', () => {
    // pin a relation/theorem-side boundary in reverse and confirm the two
    // engines agree on whether reordering changes the class
    const multi = corpus.filter((i) => i.boundary !== undefined && i.boundary.length >= 2)
    expect(multi.length).toBeGreaterThan(0)
    for (const it of multi) {
      const rev = [...it.boundary!].reverse()
      const oldSame = boundaryFingerprint(mkDiagramWithBoundary(it.diagram, it.boundary!))
        === boundaryFingerprint(mkDiagramWithBoundary(it.diagram, rev))
      const newSame = exploreForm(it.diagram, it.boundary!) === exploreForm(it.diagram, rev)
      expect(newSame, `pin-order agreement on '${it.label}'`).toBe(oldSame)
    }
  })
})
