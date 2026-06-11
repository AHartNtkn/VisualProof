import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { diagramFingerprint } from '../../../src/kernel/diagram/canonical/fingerprint'
import { replayProof } from '../../../src/kernel/proof/step'
import type { ProofContext, ProofStep } from '../../../src/kernel/proof/step'
import { composeProofs } from '../../../src/kernel/proof/compose'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)
const ctx: ProofContext = { definitions: {}, theorems: new Map() }

/** Two independently built, differently-id'd copies of the same diagram. */
function twoCopies() {
  const a = new DiagramBuilder()
  const an = a.termNode(a.root, p('y'))
  const ahub = a.termNode(a.root, p('\\x. x'))
  a.wire(a.root, [
    { node: an, port: { kind: 'freeVar', name: 'y' } },
    { node: ahub, port: { kind: 'output' } },
  ])
  const b = new DiagramBuilder()
  // build in a DIFFERENT order so ids differ structurally
  const bhub = b.termNode(b.root, p('\\x. x'))
  const bn = b.termNode(b.root, p('y'))
  b.wire(b.root, [
    { node: bn, port: { kind: 'freeVar', name: 'y' } },
    { node: bhub, port: { kind: 'output' } },
  ])
  return { da: a.build(), db: b.build(), bn }
}

describe('composeProofs', () => {
  it('rewrites a backward tail onto the forward meet and replays end to end', () => {
    const { da, db, bn } = twoCopies()
    // backward tail (recorded against db): wrap the y-node in a double cut
    const tail: ProofStep[] = [{
      rule: 'doubleCutIntro',
      sel: mkSelection(db, { region: db.root, regions: [], nodes: [bn], wires: [] }),
    }]
    const composed = composeProofs(da, db, tail, ctx)
    const viaA = replayProof(da, composed, ctx)
    const viaB = replayProof(db, tail, ctx)
    expect(diagramFingerprint(viaA)).toBe(diagramFingerprint(viaB))
  })

  it('handles multi-step tails whose later steps reference ids created by earlier ones', () => {
    const { da, db, bn } = twoCopies()
    const wrapped = replayProof(db, [{
      rule: 'doubleCutIntro',
      sel: mkSelection(db, { region: db.root, regions: [], nodes: [bn], wires: [] }),
    }], ctx)
    // find the new outer cut in the b-side result, then eliminate it again
    const outer = Object.entries(wrapped.regions)
      .find(([id, r]) => r.kind === 'cut' && db.regions[id] === undefined && r.parent === db.root)![0]
    const tail: ProofStep[] = [
      { rule: 'doubleCutIntro', sel: mkSelection(db, { region: db.root, regions: [], nodes: [bn], wires: [] }) },
      { rule: 'doubleCutElim', region: outer },
    ]
    const composed = composeProofs(da, db, tail, ctx)
    const viaA = replayProof(da, composed, ctx)
    expect(diagramFingerprint(viaA)).toBe(diagramFingerprint(da))
  })

  it('works across automorphic diagrams (two identical nodes)', () => {
    const mk = () => {
      const h = new DiagramBuilder()
      const n1 = h.termNode(h.root, p('\\x. x'))
      h.termNode(h.root, p('\\x. x'))
      return { d: h.build(), n1 }
    }
    const { d: da } = mk()
    const { d: db, n1: bn1 } = mk()
    const tail: ProofStep[] = [{
      rule: 'erasure',
      sel: mkSelection(db, { region: db.root, regions: [], nodes: [bn1], wires: [] }),
    }]
    const composed = composeProofs(da, db, tail, ctx)
    const viaA = replayProof(da, composed, ctx)
    expect(Object.values(viaA.nodes)).toHaveLength(1)
  })

  it('maps erasure sel through the iso — erases the correct node in an asymmetric meet', () => {
    // Two distinguishable nodes: identity and a constant. Build the two copies
    // in DIFFERENT orders so ids are swapped (identity='n0' in db, identity='n1' in da).
    // The tail erases the identity node. Without id mapping, the composed step
    // references a db node id that exists in da but points to the CONSTANT node,
    // erasing the wrong node and producing a non-isomorphic result.
    const bA = new DiagramBuilder()
    bA.termNode(bA.root, p('\\a. \\b. a'))  // constant gets 'n0' in da
    bA.termNode(bA.root, p('\\x. x'))       // identity gets 'n1' in da
    const da = bA.build()

    const bB = new DiagramBuilder()
    const bn1 = bB.termNode(bB.root, p('\\x. x'))       // identity gets 'n0' in db
    bB.termNode(bB.root, p('\\a. \\b. a'))              // constant gets 'n1' in db
    const db = bB.build()

    const tail: ProofStep[] = [{
      rule: 'erasure',
      sel: mkSelection(db, { region: db.root, regions: [], nodes: [bn1], wires: [] }),
    }]
    const composed = composeProofs(da, db, tail, ctx)
    const viaA = replayProof(da, composed, ctx)
    const viaB = replayProof(db, tail, ctx)
    // Both results should have the constant node only
    expect(Object.values(viaA.nodes)).toHaveLength(1)
    // Fingerprints must match — the same (constant) node survives on both sides
    expect(diagramFingerprint(viaA)).toBe(diagramFingerprint(viaB))
  })

  it('maps comprehensionInstantiate binder targets through the iso', () => {
    // Marker-first vs marker-last builds give the ∃-chain DIFFERENT region
    // ids: db's rOuter id names the chain CUT in da. An unmapped binder
    // target therefore points at a cut — refused inside the composed replay —
    // while the mapped target lands on da's rOuter and the sides agree.
    const mk = (markerFirst: boolean) => {
      const h = new DiagramBuilder()
      const marker = () => {
        const c = h.cut(h.root)
        h.termNode(c, p('\\a. \\b. a'))
      }
      if (markerFirst) marker()
      const cut = h.cut(h.root)
      const rOuter = h.bubble(cut, 1)
      const rInner = h.bubble(rOuter, 1)
      const a = h.atom(rInner, rInner)
      const t = h.termNode(rInner, p('\\x. x'))
      h.wire(rInner, [
        { node: a, port: { kind: 'arg', index: 0 } },
        { node: t, port: { kind: 'output' } },
      ])
      if (!markerFirst) marker()
      return { d: h.build(), rOuter, rInner }
    }
    const { d: da } = mk(true)
    const { d: db, rOuter: bOuter, rInner: bInner } = mk(false)

    // the open comp "x : R′(x)"
    const c = new DiagramBuilder()
    const stub = c.bubble(c.root, 1)
    const atom = c.atom(stub, stub)
    const bx = c.wire(c.root, [{ node: atom, port: { kind: 'arg', index: 0 } }])
    const comp = mkDiagramWithBoundary(c.build(), [bx])

    const tail: ProofStep[] = [
      { rule: 'comprehensionInstantiate', bubble: bInner, comp, binders: { [stub]: bOuter } },
    ]
    const composed = composeProofs(da, db, tail, ctx)
    const viaA = replayProof(da, composed, ctx)
    const viaB = replayProof(db, tail, ctx)
    expect(diagramFingerprint(viaA)).toBe(diagramFingerprint(viaB))
  })

  it('refuses non-isomorphic meets by name', () => {
    const { da } = twoCopies()
    const other = new DiagramBuilder()
    other.termNode(other.root, p('y'))
    expect(() => composeProofs(da, other.build(), [], ctx))
      .toThrowError(/do not meet/)
  })
})
