import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { exploreForm } from '../../../src/kernel/diagram/canonical/explore'
import { relSig } from '../../../src/kernel/diagram/sig'
import { replayActions, singleStepAction } from '../../../src/kernel/proof/action'
import { composeActions } from '../../../src/kernel/proof/compose'
import { EMPTY_PROOF_CONTEXT } from '../../../src/kernel/proof/context'
import { replayProof, type ProofStep } from '../../../src/kernel/proof/step'
import {
  bareWireAssembly,
  bareWireDescription,
} from '../../../src/kernel/rules/identity-rules'
import { bareWire } from '../../fixtures/pins'

describe('atom and vacuous proof steps', () => {
  it('replays atom spawn and the bare vacuous pair end to end', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const diagram = builder.build()
    const introduced = replayProof(diagram, [{
      rule: 'vacuity',
      direction: 'insert',
      assembly: bareWireAssembly('bare', diagram.root, relSig([])),
    }], EMPTY_PROOF_CONTEXT)
    const relationWire = Object.keys(introduced.wires).find((wire) =>
      diagram.wires[wire] === undefined)!
    const removal = bareWireDescription(introduced, relationWire)

    expect(() => replayProof(introduced, [
      { rule: 'atomSpawn', region: cut, wire: relationWire },
      { rule: 'vacuity', direction: 'delete', assembly: removal },
    ], EMPTY_PROOF_CONTEXT)).toThrowError(
      /step 1 \(vacuity\) failed: vacuity deletion: wire '.*' does not match/,
    )

    const restored = replayProof(introduced, [{
      rule: 'vacuity',
      direction: 'delete',
      assembly: removal,
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
      rule: 'vacuity',
      direction: 'insert',
      assembly: bareWireAssembly('bare', source.diagram.root, relSig([])),
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
      const wire = bareWire(builder, builder.root, relSig([]))
      return { diagram: builder.build(), wire }
    }
    const target = build()
    const source = build()
    const tail = [singleStepAction('remove vacuity', {
      rule: 'vacuity',
      direction: 'delete',
      assembly: bareWireDescription(source.diagram, source.wire),
    })]
    const composed = composeActions(
      target.diagram,
      source.diagram,
      tail,
      EMPTY_PROOF_CONTEXT,
    )

    expect(composed[0]!.steps[0]).toEqual({
      rule: 'vacuity',
      direction: 'delete',
      assembly: bareWireDescription(target.diagram, target.wire),
    })
  })
})
