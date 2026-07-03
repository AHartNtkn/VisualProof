import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { exploreForm } from '../../../src/kernel/diagram/canonical/explore'
import { replayProof } from '../../../src/kernel/proof/step'
import type { ProofContext, ProofStep } from '../../../src/kernel/proof/step'
import { composeProofs } from '../../../src/kernel/proof/compose'
import { stepToJson, stepFromJson } from '../../../src/kernel/proof/json'

const p = (s: string) => parseTerm(s)
const ctx: ProofContext = { theorems: new Map(), relations: new Map() }

function openPattern() {
  const b = new DiagramBuilder()
  const stub = b.bubble(b.root, 1)
  const bn = b.termNode(stub, p('\\x. x'))
  const ba = b.atom(stub, stub)
  b.wire(stub, [
    { node: bn, port: { kind: 'output' } },
    { node: ba, port: { kind: 'arg', index: 0 } },
  ])
  return { pattern: mkDiagramWithBoundary(b.build(), []), stub }
}

describe('open and vacuous proof steps', () => {
  it('replays an open insertion and the vacuous pair end to end', () => {
    const h = new DiagramBuilder()
    const cut1 = h.cut(h.root)
    const n = h.termNode(cut1, p('y'))
    const d = h.build()
    const { pattern, stub } = openPattern()
    const steps: ProofStep[] = [
      { rule: 'vacuousIntro', sel: mkSelection(d, { region: cut1, regions: [], nodes: [n], wires: [] }), arity: 1 },
    ]
    const wrapped = replayProof(d, steps, ctx)
    const bub = Object.entries(wrapped.regions).find(
      ([id, r]) => r.kind === 'bubble' && d.regions[id] === undefined,
    )![0]
    const more: ProofStep[] = [
      { rule: 'insertion', region: bub, pattern, attachments: [], binders: { [stub]: bub } },
      { rule: 'vacuousElim', region: bub },
    ]
    // vacuousElim must now REFUSE: the bubble binds the inserted atom
    expect(() => replayProof(wrapped, more, ctx)).toThrowError(/step 1 \(vacuousElim\) failed: bubble .* binds 1 atom/)
    // without the insertion the pair round-trips
    const back = replayProof(wrapped, [{ rule: 'vacuousElim', region: bub }], ctx)
    expect(exploreForm(back)).toBe(exploreForm(d))
  })

  it('round-trips the new step shapes through JSON', () => {
    const { pattern, stub } = openPattern()
    const sel = { region: 'r0', regions: [], nodes: ['n0'], wires: [] }
    const steps: ProofStep[] = [
      { rule: 'insertion', region: 'r1', pattern, attachments: ['w0'], binders: { [stub]: 'rHost' } },
      { rule: 'vacuousIntro', sel, arity: 3 },
      { rule: 'vacuousElim', region: 'r1' },
    ]
    for (const s of steps) {
      expect(stepFromJson(JSON.parse(JSON.stringify(stepToJson(s))))).toEqual(s)
    }
  })

  it('rejects malformed new fields loudly', () => {
    expect(() => stepFromJson({ rule: 'vacuousIntro', sel: { region: 'r0', regions: [], nodes: [], wires: [] }, arity: -1 }))
      .toThrowError(/arity/)
    expect(() => stepFromJson({ rule: 'insertion', region: 'r1', pattern: { diagram: { root: 'x', regions: { x: { kind: 'sheet' } }, nodes: {}, wires: {} }, boundary: [] }, attachments: [], binders: { a: 1 } }))
      .toThrowError(/binders/)
  })

  it('composeProofs maps vacuous step ids through the iso', () => {
    const mk = () => {
      const h = new DiagramBuilder()
      const cut1 = h.cut(h.root)
      const n = h.termNode(cut1, p('y'))
      return { d: h.build(), cut1, n }
    }
    const { d: da } = mk()
    const { d: db, cut1: bc, n: bn } = mk()
    const tail: ProofStep[] = [
      { rule: 'vacuousIntro', sel: mkSelection(db, { region: bc, regions: [], nodes: [bn], wires: [] }), arity: 1 },
    ]
    const composed = composeProofs(da, db, tail, ctx)
    const viaA = replayProof(da, composed, ctx)
    const viaB = replayProof(db, tail, ctx)
    expect(exploreForm(viaA)).toBe(exploreForm(viaB))
  })

  it('composeProofs maps insertion binder VALUES through a NON-IDENTITY iso', () => {
    // Isomorphic hosts with DIFFERENT ids for the host bubble: in da the
    // bubble is r2 and r3 is a bare cut; in db the bubble is r3 and r1 is the
    // bare cut. An unmapped binder VALUE ('r3') would point at da's CUT —
    // splice must see the iso image (da's bubble), or composition is wrong.
    const mkA = () => {
      const h = new DiagramBuilder()
      const c = h.cut(h.root) // r1
      const bub = h.bubble(c, 1) // r2
      h.cut(h.root) // r3 (bare cut)
      return { d: h.build(), bub }
    }
    const mkB = () => {
      const h = new DiagramBuilder()
      h.cut(h.root) // r1 (bare cut)
      const c = h.cut(h.root) // r2
      const bub = h.bubble(c, 1) // r3
      return { d: h.build(), bub }
    }
    const { d: da, bub: aBub } = mkA()
    const { d: db, bub: bBub } = mkB()
    expect(aBub).not.toBe(bBub) // the iso is non-identity on the bubble
    const { pattern, stub } = openPattern()
    const tail: ProofStep[] = [
      { rule: 'insertion', region: bBub, pattern, attachments: [], binders: { [stub]: bBub } },
    ]
    const composed = composeProofs(da, db, tail, ctx)
    const viaA = replayProof(da, composed, ctx)
    const viaB = replayProof(db, tail, ctx)
    expect(exploreForm(viaA)).toBe(exploreForm(viaB))
  })
})
