import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { exploreForm } from '../../../src/kernel/diagram/canonical/explore'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
import {
  applyAction,
  replayActions,
  singleStepAction,
  type ProofAction,
} from '../../../src/kernel/proof/action'
import { EMPTY_PROOF_CONTEXT, verifyTheory } from '../../../src/kernel/proof/context'
import { applyStep, type ProofStep } from '../../../src/kernel/proof/step'
import { bareWire } from '../../fixtures/pins'

function negativeStart() {
  const builder = new DiagramBuilder()
  const cut = builder.cut(builder.root)
  const first = bareWire(builder, builder.root, relSig([]))
  const second = bareWire(builder, builder.root, relSig([]))
  return { diagram: builder.build(), cut, first, second }
}

describe('proof actions', () => {
  it('replays a one-step action exactly like its primitive step', () => {
    const { diagram, cut, first } = negativeStart()
    const step: ProofStep = {
      rule: 'atomSpawn',
      region: cut,
      wire: first,
    }

    expect(exploreForm(applyAction(
      diagram,
      singleStepAction('spawn atom', step),
      EMPTY_PROOF_CONTEXT,
    ))).toBe(exploreForm(applyStep(
      diagram,
      step,
      EMPTY_PROOF_CONTEXT,
    )))
  })

  it('reports one action unit while replaying constituent steps in order', () => {
    const { diagram, cut, first, second } = negativeStart()
    const grouped: ProofAction = {
      label: 'spawn two atoms',
      steps: [
        { rule: 'atomSpawn', region: cut, wire: first },
        { rule: 'atomSpawn', region: cut, wire: second },
      ],
      placements: [],
    }
    const seen: Array<{ action: number; step: number; nodes: number }> = []

    const result = replayActions(
      diagram,
      [grouped],
      EMPTY_PROOF_CONTEXT,
      (next, actionIndex, stepIndex) => {
        seen.push({
          action: actionIndex,
          step: stepIndex,
          nodes: Object.keys(next.nodes).length,
        })
      },
    )

    // The start already holds four nodes: a pin at each end of both bare
    // wires. Each step adds exactly one atom on top of those.
    expect(seen).toEqual([
      { action: 0, step: 0, nodes: 5 },
      { action: 0, step: 1, nodes: 6 },
    ])
    expect(Object.keys(result.nodes)).toHaveLength(6)
  })

  it('excludes action-reserved node and wire ids', () => {
    const bodyBuilder = new DiagramBuilder()
    const boundary = bodyBuilder.wire([], IOTA)
    const context = verifyTheory({
      relations: [[
        'Unary',
        bodyBuilder.buildOpen([boundary]),
      ]],
      theorems: [],
    })
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const diagram = builder.build()
    const reserved: ProofAction = {
      label: 'reserved ref',
      steps: [{
        rule: 'refSpawn',
        region: cut,
        defId: 'Unary',
        sig: relSig([IOTA]),
      }],
      placements: [],
      allocation: {
        regions: [],
        nodes: ['n'],
        wires: ['w'],
      },
    }

    const result = applyAction(diagram, reserved, context)

    // The reserved bases are skipped; the ref's fresh argument wire also
    // brings the pin that holds its quantifier, whose base is not reserved.
    expect(Object.keys(result.nodes)).toEqual(['n_0', 'pin'])
    expect(Object.keys(result.wires)).toEqual(['w_0'])
  })

  it('rejects malformed allocation before applying a step', () => {
    const { diagram, cut, first } = negativeStart()
    const duplicate = {
      label: 'duplicate reservation',
      steps: [{ rule: 'atomSpawn', region: cut, wire: first }],
      placements: [],
      allocation: {
        regions: [],
        nodes: ['reserved', 'reserved'],
        wires: [],
      },
    } as unknown as ProofAction
    expect(() => applyAction(diagram, duplicate, EMPTY_PROOF_CONTEXT))
      .toThrowError(/duplicate.*node.*reserved/i)

    const incomplete = {
      ...duplicate,
      allocation: { regions: [], nodes: [] },
    } as unknown as ProofAction
    expect(() => applyAction(diagram, incomplete, EMPTY_PROOF_CONTEXT))
      .toThrowError(/allocation wires must be an array/i)
  })

  it('excludes reserved region ids from double-cut allocation', () => {
    const diagram = new DiagramBuilder().build()
    const action: ProofAction = {
      label: 'reserved double cut',
      steps: [{
        rule: 'doubleCutIntro',
        sel: {
          region: diagram.root,
          regions: [],
          nodes: [],
          wires: [],
        },
      }],
      placements: [],
      allocation: {
        regions: ['dc', 'dc_0'],
        nodes: [],
        wires: [],
      },
    }

    const result = applyAction(
      diagram,
      action,
      EMPTY_PROOF_CONTEXT,
    )
    expect(Object.keys(result.regions).filter((id) =>
      diagram.regions[id] === undefined)).toEqual(['dc_1', 'dc_2'])
  })

  it('identifies both action and constituent step on failure', () => {
    const { diagram, cut, first } = negativeStart()
    const action: ProofAction = {
      label: 'bad grouped gesture',
      steps: [
        { rule: 'atomSpawn', region: cut, wire: first },
        {
          rule: 'erasure',
          sel: { region: cut, regions: [], nodes: ['n'], wires: [] },
        },
      ],
      placements: [],
    }

    expect(() => replayActions(
      diagram,
      [action],
      EMPTY_PROOF_CONTEXT,
    )).toThrowError(/action 0 .* step 1 \(erasure\) failed/)
  })

  it('validates placement indices against all introduced nodes', () => {
    const { diagram, cut, first, second } = negativeStart()
    const steps: readonly ProofStep[] = [
      { rule: 'atomSpawn', region: cut, wire: first },
      { rule: 'atomSpawn', region: cut, wire: second },
    ]
    const valid: ProofAction = {
      label: 'placed pair',
      steps,
      placements: [
        { introducedNode: 0, x: 10, y: -5 },
        { introducedNode: 1, x: 20, y: 15 },
      ],
    }

    expect(applyAction(diagram, valid, EMPTY_PROOF_CONTEXT)).toEqual(
      applyAction(
        diagram,
        { ...valid, placements: [] },
        EMPTY_PROOF_CONTEXT,
      ),
    )
    expect(() => applyAction(diagram, {
      ...valid,
      placements: [{ introducedNode: 2, x: 0, y: 0 }],
    }, EMPTY_PROOF_CONTEXT)).toThrowError(/index 2 is out of range/)
    expect(() => applyAction(diagram, {
      ...valid,
      placements: [
        { introducedNode: 0, x: 0, y: 0 },
        { introducedNode: 0, x: 1, y: 1 },
      ],
    }, EMPTY_PROOF_CONTEXT)).toThrowError(/duplicate introduced node index 0/)
    expect(() => applyAction(diagram, {
      ...valid,
      placements: [{ introducedNode: 0, x: Number.NaN, y: 0 }],
    }, EMPTY_PROOF_CONTEXT)).toThrowError(/coordinates must be finite/)
  })

  it('rejects actions without a label or a primitive step', () => {
    const { diagram, cut, first } = negativeStart()
    const step: ProofStep = {
      rule: 'atomSpawn',
      region: cut,
      wire: first,
    }
    expect(() => applyAction(
      diagram,
      { label: '', steps: [step], placements: [] },
      EMPTY_PROOF_CONTEXT,
    )).toThrowError(/label must not be empty/)
    expect(() => applyAction(
      diagram,
      { label: 'empty', steps: [], placements: [] },
      EMPTY_PROOF_CONTEXT,
    )).toThrowError(/must contain at least one step/)
  })
})
