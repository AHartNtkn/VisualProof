import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { exploreForm } from '../../../src/kernel/diagram/canonical/explore'
import type { Diagram } from '../../../src/kernel/diagram/diagram'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
import {
  mkSelection,
  type SubgraphSelection,
} from '../../../src/kernel/diagram/subgraph/selection'
import { applyDoubleCutElim, applyDoubleCutIntro } from '../../../src/kernel/rules/doublecut'
import { applyErasure } from '../../../src/kernel/rules/erasure'
import { applyIdentityInsertion } from '../../../src/kernel/rules/identity'
import {
  applyDeiteration,
  applyIteration,
  findDeiterationEvidence,
} from '../../../src/kernel/rules/iteration'

function nested(depth: number) {
  const builder = new DiagramBuilder()
  let region = builder.root
  for (let index = 0; index < depth; index++) region = builder.cut(region)
  const node = builder.ref(region, 'closed', relSig([]))
  const left = builder.wire(builder.root, [])
  const right = builder.wire(builder.root, [])
  return { diagram: builder.build(), region, node, left, right }
}

describe('polarity matrix across depths 0–3', () => {
  for (let depth = 0; depth <= 3; depth++) {
    const positive = depth % 2 === 0

    it(`depth ${depth} (${positive ? 'positive' : 'negative'}): identity insertion and erasure are complementary`, () => {
      const { diagram, region, node, left, right } = nested(depth)
      const selection = mkSelection(diagram, {
        region,
        regions: [],
        nodes: [node],
        wires: [],
      })

      if (positive) {
        expect(() => applyIdentityInsertion(diagram, region, [left, right]))
          .toThrowError(/identity insertion requires a negative region/)
        expect(() => applyErasure(diagram, selection)).not.toThrow()
      } else {
        expect(() => applyIdentityInsertion(diagram, region, [left, right])).not.toThrow()
        expect(() => applyErasure(diagram, selection))
          .toThrowError(/erasure requires a positive region/)
        const legacyShape = applyErasure as unknown as (
          d: Diagram,
          selection: SubgraphSelection,
          orientation: string,
        ) => Diagram
        expect(() => legacyShape(diagram, selection, 'backward'))
          .toThrowError(/erasure requires a positive region/)
      }
    })

    it(`depth ${depth}: iteration and double-cut rules remain polarity-free`, () => {
      const { diagram, region, node } = nested(depth)
      const selection = mkSelection(diagram, {
        region,
        regions: [],
        nodes: [node],
        wires: [],
      })

      expect(() => applyIteration(diagram, selection, region)).not.toThrow()
      expect(() => applyDoubleCutIntro(diagram, selection)).not.toThrow()
    })
  }
})

describe('structural round trips', () => {
  it('double-cut introduction and elimination round-trip at every depth', () => {
    for (let depth = 0; depth <= 2; depth++) {
      const { diagram, region, node } = nested(depth)
      const selection = mkSelection(diagram, {
        region,
        regions: [],
        nodes: [node],
        wires: [],
      })
      const wrapped = applyDoubleCutIntro(diagram, selection)
      const outer = Object.entries(wrapped.regions).find(
        ([id, candidate]) =>
          id !== region
          && candidate.kind === 'cut'
          && candidate.parent === region
          && diagram.regions[id] === undefined,
      )![0]

      expect(exploreForm(applyDoubleCutElim(wrapped, outer)))
        .toBe(exploreForm(diagram))
    }
  })

  it('iteration into a cut and exact deiteration round-trip under nesting', () => {
    const builder = new DiagramBuilder()
    const target = builder.cut(builder.root)
    const node = builder.ref(builder.root, 'P', relSig([IOTA]))
    builder.wire(builder.root, [
      { node, port: { kind: 'arg', index: 0 } },
    ])
    const diagram = builder.build()
    const selection = mkSelection(diagram, {
      region: diagram.root,
      regions: [],
      nodes: [node],
      wires: [],
    })
    const iterated = applyIteration(diagram, selection, target)
    const copy = Object.entries(iterated.nodes)
      .find(([id, candidate]) => id !== node && candidate.region === target)![0]
    const copySelection = mkSelection(iterated, {
      region: target,
      regions: [],
      nodes: [copy],
      wires: [],
    })
    const evidence = findDeiterationEvidence(iterated, copySelection, 10_000)

    expect(exploreForm(applyDeiteration(
      iterated,
      copySelection,
      evidence.justifier,
      evidence.certificate,
    ))).toBe(exploreForm(diagram))
  })
})
