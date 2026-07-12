import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { exploreForm } from '../../../src/kernel/diagram/canonical/explore'
import { replayProof } from '../../../src/kernel/proof/step'
import type { ProofContext, ProofStep } from '../../../src/kernel/proof/step'
import { composeProofs } from '../../../src/kernel/proof/compose'
import { stepToJson, stepFromJson } from '../../../src/kernel/proof/json'

const p = (s: string) => parseTerm(s)
const ctx: ProofContext = { theorems: new Map(), relations: new Map() }

describe('open and vacuous proof steps', () => {
  it('replays bound relation spawning and the vacuous pair end to end', () => {
    const h = new DiagramBuilder()
    const cut1 = h.cut(h.root)
    const n = h.termNode(cut1, p('y'))
    const d = h.build()
    const steps: ProofStep[] = [
      { rule: 'vacuousIntro', sel: mkSelection(d, { region: cut1, regions: [], nodes: [n], wires: [] }), arity: 1 },
    ]
    const wrapped = replayProof(d, steps, ctx)
    const bub = Object.entries(wrapped.regions).find(
      ([id, r]) => r.kind === 'bubble' && d.regions[id] === undefined,
    )![0]
    const more: ProofStep[] = [
      { rule: 'boundRelationSpawn', region: bub, binder: bub },
      { rule: 'vacuousElim', region: bub },
    ]
    // vacuousElim must now REFUSE: the bubble binds the spawned atom
    expect(() => replayProof(wrapped, more, ctx)).toThrowError(/step 1 \(vacuousElim\) failed: bubble .* binds 1 atom/)
    // without spawning a bound atom the pair round-trips
    const back = replayProof(wrapped, [{ rule: 'vacuousElim', region: bub }], ctx)
    expect(exploreForm(back)).toBe(exploreForm(d))
  })

  it('round-trips the new step shapes through JSON', () => {
    const sel = { region: 'r0', regions: [], nodes: ['n0'], wires: [] }
    const steps: ProofStep[] = [
      { rule: 'openTermSpawn', region: 'r1', term: p('x') },
      { rule: 'relationSpawn', region: 'r1', defId: 'nat', arity: 1 },
      { rule: 'boundRelationSpawn', region: 'r1', binder: 'rHost' },
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
    expect(() => stepFromJson({ rule: 'insertion', region: 'r1' })).toThrowError(/unknown rule 'insertion'/)
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

  it('composeProofs maps bound-spawn binder ids through a NON-IDENTITY iso', () => {
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
    const tail: ProofStep[] = [
      { rule: 'boundRelationSpawn', region: bBub, binder: bBub },
    ]
    const composed = composeProofs(da, db, tail, ctx)
    const viaA = replayProof(da, composed, ctx)
    const viaB = replayProof(db, tail, ctx)
    expect(exploreForm(viaA)).toBe(exploreForm(viaB))
  })
})
