import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { relSig, TERM } from '../../../src/kernel/diagram/sig'
import { exploreForm } from '../../../src/kernel/diagram/canonical/explore'
import { replayProof } from '../../../src/kernel/proof/step'
import { EMPTY_PROOF_CONTEXT, type ProofContext } from '../../../src/kernel/proof/context'
import type { ProofStep } from '../../../src/kernel/proof/step'
import { composeActions } from '../../../src/kernel/proof/compose'
import { replayActions, singleStepAction } from '../../../src/kernel/proof/action'

const p = (s: string) => parseTerm(s)
const ctx: ProofContext = EMPTY_PROOF_CONTEXT
const arity1 = relSig([TERM])

// JSON round-trip and malformed-field coverage for these step shapes lives
// in tests/kernel/proof/json.test.ts (comprehensive over every step kind).
// This file covers what that one doesn't: end-to-end proof-step replay of
// the vacuous/bound-relation pair, and composeActions mapping their ids
// through an isomorphism.

describe('open and vacuous proof steps', () => {
  it('replays bound relation spawning and the vacuous pair end to end', () => {
    const h = new DiagramBuilder()
    const cut1 = h.cut(h.root)
    h.termNode(cut1, p('y'))
    const d = h.build()
    const steps: ProofStep[] = [
      { rule: 'vacuousIntro', scope: cut1, sig: arity1 },
    ]
    const wrapped = replayProof(d, steps, ctx)
    const relWire = Object.entries(wrapped.wires).find(
      ([id, w]) => w.sig.kind === 'rel' && d.wires[id] === undefined,
    )![0]
    const more: ProofStep[] = [
      { rule: 'boundRelationSpawn', region: cut1, wire: relWire },
      { rule: 'vacuousElim', wireId: relWire },
    ]
    // vacuousElim must now REFUSE: the wire carries the spawned atom's head
    expect(() => replayProof(wrapped, more, ctx)).toThrowError(/step 1 \(vacuousElim\) failed: vacuous elimination requires an endpoint-free wire/)
    // without spawning a bound atom the pair round-trips
    const back = replayProof(wrapped, [{ rule: 'vacuousElim', wireId: relWire }], ctx)
    expect(exploreForm(back)).toBe(exploreForm(d))
  })

  it('composeActions maps vacuous step ids through the iso', () => {
    const mk = () => {
      const h = new DiagramBuilder()
      const cut1 = h.cut(h.root)
      h.termNode(cut1, p('y'))
      return { d: h.build(), cut1 }
    }
    const { d: da } = mk()
    const { d: db, cut1: bc } = mk()
    const tail: ProofStep[] = [
      { rule: 'vacuousIntro', scope: bc, sig: arity1 },
    ]
    const actions = tail.map((step) => singleStepAction(step.rule, step))
    const composed = composeActions(da, db, actions, ctx)
    const viaA = replayActions(da, composed, ctx)
    const viaB = replayProof(db, tail, ctx)
    expect(exploreForm(viaA)).toBe(exploreForm(viaB))
  })

  it('composeActions maps bound-spawn wire ids through a NON-IDENTITY iso', () => {
    // Isomorphic hosts with DIFFERENT ids for the relational wire: in da the
    // wire is w1 (an unrelated empty TERM wire is w0); in db the relational
    // wire is w0 (the unrelated TERM wire is w1). An unmapped wire VALUE
    // ('w0') would point at da's TERM wire — splice must see the iso image
    // (da's relational wire), or composition is wrong.
    const mkA = () => {
      const h = new DiagramBuilder()
      const c = h.cut(h.root) // r1
      h.wire(h.root, []) // w0: unrelated empty TERM wire, shifts numbering
      const rel = h.relWire(c, arity1) // w1
      return { d: h.build(), rel, region: c }
    }
    const mkB = () => {
      const h = new DiagramBuilder()
      const c = h.cut(h.root) // r1
      const rel = h.relWire(c, arity1) // w0
      h.wire(h.root, []) // w1: unrelated empty TERM wire
      return { d: h.build(), rel, region: c }
    }
    const { d: da, rel: aRel } = mkA()
    const { d: db, rel: bRel, region: bRegion } = mkB()
    expect(aRel).not.toBe(bRel) // the iso is non-identity on the relational wire
    const tail: ProofStep[] = [
      { rule: 'boundRelationSpawn', region: bRegion, wire: bRel },
    ]
    const composed = composeActions(da, db, tail.map((step) => singleStepAction(step.rule, step)), ctx)
    const viaA = replayActions(da, composed, ctx)
    const viaB = replayProof(db, tail, ctx)
    expect(exploreForm(viaA)).toBe(exploreForm(viaB))
  })
})
