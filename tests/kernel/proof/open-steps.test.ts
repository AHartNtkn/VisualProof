import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { exploreForm } from '../../../src/kernel/diagram/canonical/explore'
import { relSig } from '../../../src/kernel/diagram/sig'
import { replayActions, singleStepAction } from '../../../src/kernel/proof/action'
import { composeActions } from '../../../src/kernel/proof/compose'
import { EMPTY_PROOF_CONTEXT } from '../../../src/kernel/proof/context'
import { replayProof, type ProofStep } from '../../../src/kernel/proof/step'

describe('atom and vacuous proof steps', () => {
  it('replays atom spawn and the bare vacuous pair end to end', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const diagram = builder.build()
    const introduced = replayProof(diagram, [{
      rule: 'vacuousIntro',
      scope: cut,
      sig: relSig([]),
    }], EMPTY_PROOF_CONTEXT)
    const relationWire = Object.keys(introduced.wires).find((wire) =>
      diagram.wires[wire] === undefined)!

    expect(() => replayProof(introduced, [
      { rule: 'atomSpawn', region: cut, wire: relationWire },
      { rule: 'vacuousElim', wireId: relationWire },
    ], EMPTY_PROOF_CONTEXT)).toThrowError(
      /step 1 \(vacuousElim\) failed: vacuous elimination requires an endpoint-free wire/,
    )

    const restored = replayProof(introduced, [{
      rule: 'vacuousElim',
      wireId: relationWire,
    }], EMPTY_PROOF_CONTEXT)
    expect(exploreForm(restored)).toBe(exploreForm(diagram))
  })

  it('composes a later atom step that names a wire minted by vacuity', () => {
    const build = (markerFirst: boolean) => {
      const builder = new DiagramBuilder()
      if (markerFirst) builder.cut(builder.root)
      const cut = builder.cut(builder.root)
      if (!markerFirst) builder.cut(builder.root)
      return { diagram: builder.build(), cut }
    }
    const target = build(true)
    const source = build(false)
    const intro: ProofStep = {
      rule: 'vacuousIntro',
      scope: source.cut,
      sig: relSig([]),
    }
    const afterIntro = replayProof(
      source.diagram,
      [intro],
      EMPTY_PROOF_CONTEXT,
    )
    const minted = Object.keys(afterIntro.wires).find((wire) =>
      source.diagram.wires[wire] === undefined)!
    const tail = [{
      label: 'introduce and bind atom',
      steps: [
        intro,
        { rule: 'atomSpawn', region: source.cut, wire: minted },
      ] as const,
      placements: [],
    }]

    const composed = composeActions(
      target.diagram,
      source.diagram,
      tail,
      EMPTY_PROOF_CONTEXT,
    )

    expect(exploreForm(replayActions(
      target.diagram,
      composed,
      EMPTY_PROOF_CONTEXT,
    ))).toBe(exploreForm(replayActions(
      source.diagram,
      tail,
      EMPTY_PROOF_CONTEXT,
    )))
  })

  it('maps a bare vacuous elimination wire across an isomorphism', () => {
    const build = () => {
      const builder = new DiagramBuilder()
      const wire = builder.relWire( relSig([]))
      return { diagram: builder.build(), wire }
    }
    const target = build()
    const source = build()
    const tail = [singleStepAction('remove vacuity', {
      rule: 'vacuousElim',
      wireId: source.wire,
    })]
    const composed = composeActions(
      target.diagram,
      source.diagram,
      tail,
      EMPTY_PROOF_CONTEXT,
    )

    expect(composed[0]!.steps[0]).toEqual({
      rule: 'vacuousElim',
      wireId: target.wire,
    })
  })
})
