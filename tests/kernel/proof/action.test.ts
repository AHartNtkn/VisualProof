import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { exploreForm } from '../../../src/kernel/diagram/canonical/explore'
import { parseTerm } from '../../../src/kernel/term/parse'
import { applyStep } from '../../../src/kernel/proof/step'
import type { ProofContext, ProofStep } from '../../../src/kernel/proof/step'
import {
  applyAction,
  replayActions,
  singleStepAction,
} from '../../../src/kernel/proof/action'
import type { ProofAction } from '../../../src/kernel/proof/action'

const ctx: ProofContext = { theorems: new Map(), relations: new Map() }
const p = (source: string) => parseTerm(source)

function negativeStart() {
  const b = new DiagramBuilder()
  const cut = b.cut(b.root)
  return { diagram: b.build(), cut }
}

describe('proof actions', () => {
  it('replays a one-step action exactly like its trusted step', () => {
    const { diagram, cut } = negativeStart()
    const step: ProofStep = { rule: 'closedTermIntro', region: cut, term: p('\\x. x') }

    expect(exploreForm(applyAction(diagram, singleStepAction('introduce identity', step), ctx)))
      .toBe(exploreForm(applyStep(diagram, step, ctx)))
  })

  it('reports one action unit while replaying every constituent step in order', () => {
    const { diagram, cut } = negativeStart()
    const action: ProofAction = {
      label: 'introduce two terms',
      steps: [
        { rule: 'closedTermIntro', region: cut, term: p('\\x. x') },
        { rule: 'closedTermIntro', region: cut, term: p('\\x. \\y. x') },
      ],
      placements: [],
    }
    const seen: Array<{ action: number; step: number; nodes: number }> = []

    const out = replayActions(diagram, [action], ctx, (d, actionIndex, stepIndex) => {
      seen.push({ action: actionIndex, step: stepIndex, nodes: Object.keys(d.nodes).length })
    })

    expect(seen).toEqual([
      { action: 0, step: 0, nodes: 1 },
      { action: 0, step: 1, nodes: 2 },
    ])
    expect(Object.keys(out.nodes)).toHaveLength(2)
  })

  it('identifies both the action and constituent step when replay fails', () => {
    const { diagram, cut } = negativeStart()
    const action: ProofAction = {
      label: 'bad grouped gesture',
      steps: [
        { rule: 'closedTermIntro', region: cut, term: p('\\x. x') },
        {
          rule: 'erasure',
          sel: { region: cut, regions: [], nodes: ['n0'], wires: [] },
        },
      ],
      placements: [],
    }

    expect(() => replayActions(diagram, [action], ctx))
      .toThrowError(/action 0 .* step 1 \(erasure\) failed/)
  })

  it('accepts placement indices only for nodes introduced by the whole action', () => {
    const { diagram, cut } = negativeStart()
    const steps: readonly ProofStep[] = [
      { rule: 'closedTermIntro', region: cut, term: p('\\x. x') },
      { rule: 'closedTermIntro', region: cut, term: p('\\x. \\y. x') },
    ]
    const valid: ProofAction = {
      label: 'placed pair', steps,
      placements: [
        { introducedNode: 0, x: 10, y: -5 },
        { introducedNode: 1, x: 20, y: 15 },
      ],
    }

    const placed = applyAction(diagram, valid, ctx)
    const unplaced = applyAction(diagram, { ...valid, placements: [] }, ctx)
    expect(placed).toEqual(unplaced)
    expect(() => applyAction(diagram, { ...valid, placements: [{ introducedNode: 2, x: 0, y: 0 }] }, ctx))
      .toThrowError(/introduced node index 2 is out of range/)
    expect(() => applyAction(diagram, { ...valid, placements: [{ introducedNode: 0, x: 0, y: 0 }, { introducedNode: 0, x: 1, y: 1 }] }, ctx))
      .toThrowError(/duplicate introduced node index 0/)
    expect(() => applyAction(diagram, { ...valid, placements: [{ introducedNode: 0, x: Number.NaN, y: 0 }] }, ctx))
      .toThrowError(/coordinates must be finite/)
  })

  it('rejects actions without a label or trusted steps', () => {
    const { diagram, cut } = negativeStart()
    const step: ProofStep = { rule: 'closedTermIntro', region: cut, term: p('\\x. x') }
    expect(() => applyAction(diagram, { label: '', steps: [step], placements: [] }, ctx))
      .toThrowError(/label must not be empty/)
    expect(() => applyAction(diagram, { label: 'empty', steps: [], placements: [] }, ctx))
      .toThrowError(/must contain at least one step/)
  })
})
