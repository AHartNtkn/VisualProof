import { describe, it, expect } from 'vitest'
import { verifyTheory } from '../../../src/kernel/proof/store'
import { buildFregeTheory } from '../../../src/theories/frege'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { applyRelFold, applyRelUnfold } from '../../../src/kernel/rules/reldef'
import { findOccurrences, occurrenceSelection } from '../../../src/kernel/diagram/subgraph/match'
import { startSession, applyBackward } from '../../../src/app/session'
import type { Diagram, NodeId } from '../../../src/kernel/diagram/diagram'

/**
 * applyRelFold must mint its reference id against the FULL pre-removal id
 * set (the applyTheorem discipline): removing the occurrence first and
 * minting after can RESURRECT a just-deleted node id, which breaks every
 * diff-based consumer (backward inverses, remapping) and the id-survival
 * reasoning checkTheorem depends on.
 */
describe('relFold id freshness', () => {
  const ctx = () => verifyTheory(buildFregeTheory())

  it('the user sequence: backward unfold nat, unfold zero, fold zero, fold nat', () => {
    const c = ctx()
    const b = new DiagramBuilder()
    const z = b.ref(b.root, 'zero', 1)
    const n = b.ref(b.root, 'nat', 1)
    b.wire(b.root, [
      { node: z, port: { kind: 'arg', index: 0 } },
      { node: n, port: { kind: 'arg', index: 0 } },
    ])
    const goal = mkDiagramWithBoundary(b.build(), [])
    let s = startSession(mkDiagramWithBoundary(new DiagramBuilder().build(), []), goal, c)
    // unfold nat (backward: relUnfold is direction-free)
    s = applyBackward(s, { rule: 'relUnfold', node: n })
    // unfold the zero INSIDE what nat left... find any zero ref
    const zeros = (d: Diagram): NodeId[] => Object.entries(d.nodes).filter(([, x]) => x.kind === 'ref' && x.defId === 'zero').map(([id]) => id)
    const innerZero = zeros(s.backward.current).find((id) => id !== z) ?? z
    s = applyBackward(s, { rule: 'relUnfold', node: innerZero })
    // fold the zero back: infer the occurrence of zero's body
    const g1 = s.backward.current
    const zBody = c.relations.get('zero')!
    void zBody
    // the fold selection is what the zero unfold spliced: infer via the matcher
    const zOcc = findOccurrences(g1, c.relations.get('zero')!, { fuel: 64, mode: 'exact' }).matches[0]!
    s = applyBackward(s, { rule: 'relFold', sel: occurrenceSelection(c.relations.get('zero')!, zOcc, g1), defId: 'zero', args: [...zOcc.attachments] })
    // fold nat back — this is where the session-bug error fired
    const g2 = s.backward.current
    const nOcc = findOccurrences(g2, c.relations.get('nat')!, { fuel: 64, mode: 'exact' }).matches[0]!
    expect(() => {
      s = applyBackward(s, { rule: 'relFold', sel: occurrenceSelection(c.relations.get('nat')!, nOcc, g2), defId: 'nat', args: [...nOcc.attachments] })
    }).not.toThrow()
  })

  it('the minted reference id never collides with a pre-fold id', () => {
    const c = ctx()
    // forward shape: unfold zero then fold it back; the new ref id must be
    // fresh against the PRE-removal diagram
    const b = new DiagramBuilder()
    const z = b.ref(b.root, 'zero', 1)
    b.wire(b.root, [{ node: z, port: { kind: 'arg', index: 0 } }])
    const d0 = b.build()
    const d1 = applyRelUnfold(d0, z, c.relations)
    const occ = findOccurrences(d1, c.relations.get('zero')!, { fuel: 64, mode: 'exact' }).matches[0]!
    const sel = occurrenceSelection(c.relations.get('zero')!, occ, d1)
    const d2 = applyRelFold(d1, sel, 'zero', [...occ.attachments], c.relations)
    const fresh = Object.keys(d2.nodes).filter((id) => d1.nodes[id] === undefined)
    expect(fresh.length, 'exactly one genuinely fresh node: the reference').toBe(1)
    expect(d2.nodes[fresh[0]!]!.kind).toBe('ref')
  })
})
