import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { sameDiagram } from '../../../src/kernel/diagram/canonical/iso'
import { relSig } from '../../../src/kernel/diagram/sig'
import { replayActions } from '../../../src/kernel/proof/action'
import { composeActions } from '../../../src/kernel/proof/compose'
import { EMPTY_PROOF_CONTEXT } from '../../../src/kernel/proof/context'
import { replayProof, type ProofStep } from '../../../src/kernel/proof/step'
import {
  bareWireDeletionSteps,
  bareWireInsertSteps,
} from '../../../src/kernel/proof/bare-wire'
import { bareWire } from '../../fixtures/pins'

describe('atom and vacuous proof steps', () => {
  it('replays atom spawn and the bare vacuous pair end to end', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const diagram = builder.build()
    const introduced = replayProof(
      diagram,
      [...bareWireInsertSteps(diagram, diagram.root, relSig([]), 'bare').steps],
      EMPTY_PROOF_CONTEXT,
    )
    const relationWire = Object.keys(introduced.wires).find((wire) =>
      diagram.wires[wire] === undefined)!
    const removal = bareWireDeletionSteps(introduced, relationWire)

    // The atom spawn gives the wire a third end, so the stale stub
    // retraction no longer matches the wire's shape.
    expect(() => replayProof(introduced, [
      { rule: 'atomSpawn', region: cut, wire: relationWire },
      ...removal,
    ], EMPTY_PROOF_CONTEXT)).toThrowError(
      /step 1 \(vacuity\) failed: vacuity deletion: wire '.*' is not a stub/,
    )

    const restored = replayProof(introduced, [...removal], EMPTY_PROOF_CONTEXT)
    expect(sameDiagram(restored, diagram)).toBe(true)
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
    const intro: readonly ProofStep[] =
      bareWireInsertSteps(source.diagram, source.diagram.root, relSig([]), 'bare').steps
    const afterIntro = replayProof(
      source.diagram,
      [...intro],
      EMPTY_PROOF_CONTEXT,
    )
    const minted = Object.keys(afterIntro.wires).find((wire) =>
      source.diagram.wires[wire] === undefined)!
    const tail = [{
      label: 'introduce and bind atom',
      steps: [
        ...intro,
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

    expect(sameDiagram(
      replayActions(
        target.diagram,
        composed,
        EMPTY_PROOF_CONTEXT,
      ),
      replayActions(
        source.diagram,
        tail,
        EMPTY_PROOF_CONTEXT,
      ),
    )).toBe(true)
  })

  it('maps a bare vacuous elimination wire across an isomorphism', () => {
    const build = () => {
      const builder = new DiagramBuilder()
      const wire = bareWire(builder, builder.root, relSig([]))
      return { diagram: builder.build(), wire }
    }
    const target = build()
    const source = build()
    const tail = [{
      label: 'remove vacuity',
      steps: [...bareWireDeletionSteps(source.diagram, source.wire)],
      placements: [],
    }]
    const composed = composeActions(
      target.diagram,
      source.diagram,
      tail,
      EMPTY_PROOF_CONTEXT,
    )

    expect(composed[0]!.steps).toEqual(
      bareWireDeletionSteps(target.diagram, target.wire),
    )
  })
})
