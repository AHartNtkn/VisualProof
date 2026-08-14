import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { sameDiagram } from '../../../src/kernel/diagram/canonical/iso'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { applyDoubleCutElim, applyDoubleCutIntro } from '../../../src/kernel/rules/doublecut'
import { applyErasure } from '../../../src/kernel/rules/erasure'
import { applyIdentityInsertion } from '../../../src/kernel/rules/identity'
import {
  applyEndsDelete,
  applyEndsSpawn,
} from '../../../src/kernel/rules/wire-content'
import {
  applyDeiteration,
  applyIteration,
  findDeiterationEvidence,
} from '../../../src/kernel/rules/iteration'
import { applyWireSever } from '../../../src/kernel/rules/wire-quantifier'
import {
  compileRelationJoin,
  compileRelationSever,
} from '../../../src/kernel/proof/compile-content'
import { bareWire } from '../../fixtures/pins'
import { EMPTY_PROOF_CONTEXT } from '../../../src/kernel/proof/context'

function nested(depth: number) {
  const builder = new DiagramBuilder()
  let region = builder.root
  for (let index = 0; index < depth; index++) region = builder.cut(region)
  const node = builder.ref(region, 'closed', relSig([]))
  const left = bareWire(builder, builder.root)
  const right = bareWire(builder, builder.root)
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
        expect(() => applyIdentityInsertion(
          diagram,
          region,
          [left, right],
          'backward',
        )).not.toThrow()
        expect(() => applyErasure(diagram, selection)).not.toThrow()
      } else {
        expect(() => applyIdentityInsertion(diagram, region, [left, right])).not.toThrow()
        expect(() => applyIdentityInsertion(
          diagram,
          region,
          [left, right],
          'backward',
        )).toThrowError(/backward identity insertion requires a positive region/)
        expect(() => applyErasure(diagram, selection))
          .toThrowError(/erasure requires a positive region/)
      }
      if (positive) {
        expect(() => applyErasure(diagram, selection, 'backward'))
          .toThrowError(/backward erasure requires a negative region/)
      } else {
        expect(() => applyErasure(diagram, selection, 'backward')).not.toThrow()
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

    it(`depth ${depth}: ends delete/spawn use complementary polarity`, () => {
      const builder = new DiagramBuilder()
      let region = builder.root
      for (let index = 0; index < depth; index++) region = builder.cut(region)
      const wire = bareWire(builder, region, relSig([]))
      const diagram = builder.build()
      const del = () => applyEndsDelete(diagram, wire)
      const delBackward = () => applyEndsDelete(diagram, wire, 'backward')
      const spawn = () => applyEndsSpawn(diagram, wire, [{ region, args: [] }])
      const spawnBackward = () =>
        applyEndsSpawn(diagram, wire, [{ region, args: [] }], 'backward')

      if (positive) {
        expect(del).toThrow()
        expect(delBackward).not.toThrow()
        expect(spawn).not.toThrow()
        expect(spawnBackward).toThrow()
      } else {
        expect(del).not.toThrow()
        expect(delBackward).toThrow()
        expect(spawn).toThrow()
        expect(spawnBackward).not.toThrow()
      }
    })

    it(`depth ${depth}: sever scope parameter gates on the chosen region`, () => {
      const { diagram, region, left } = nested(depth)
      // The bare wire's pins stay where they are, so nothing moves into the
      // chosen region and only its polarity is under test.
      const keep = diagram.wires[left]!.endpoints
      const scoped = () => applyWireSever(diagram, {
        wire: left,
        keep,
        scope: region,
      })
      const scopedBackward = () => applyWireSever(diagram, {
        wire: left,
        keep,
        scope: region,
      }, 'backward')

      if (positive) {
        expect(scoped).not.toThrow()
        expect(scopedBackward).toThrow()
      } else {
        expect(scoped).toThrow()
        expect(scopedBackward).not.toThrow()
      }
    })

    it(`depth ${depth}: compiled relation abstraction/grounding use complementary polarity`, () => {
      const builder = new DiagramBuilder()
      let region = builder.root
      for (let index = 0; index < depth; index++) region = builder.cut(region)
      const relation = bareWire(builder, region, relSig([]))
      const diagram = builder.build()
      const content = new DiagramBuilder().buildOpen([])
      const severInput = {
        scope: region,
        occurrences: [{
          sel: { region, regions: [], nodes: [], wires: [] },
          args: [],
        }],
      } as const
      const sever = () =>
        compileRelationSever(diagram, severInput, EMPTY_PROOF_CONTEXT)
      const severBackward = () =>
        compileRelationSever(diagram, severInput, EMPTY_PROOF_CONTEXT, 'backward')
      const join = () => compileRelationJoin(
        diagram,
        relation,
        content,
        [],
        EMPTY_PROOF_CONTEXT,
      )
      const joinBackward = () => compileRelationJoin(
        diagram,
        relation,
        content,
        [],
        EMPTY_PROOF_CONTEXT,
        'backward',
      )

      if (positive) {
        expect(sever).not.toThrow()
        expect(severBackward).toThrow()
        expect(join).toThrow()
        expect(joinBackward).not.toThrow()
      } else {
        expect(sever).toThrow()
        expect(severBackward).not.toThrow()
        expect(join).not.toThrow()
        expect(joinBackward).toThrow()
      }
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

      expect(sameDiagram(applyDoubleCutElim(wrapped, outer), diagram)).toBe(true)
    }
  })

  it('iteration into a cut and exact deiteration round-trip under nesting', () => {
    const builder = new DiagramBuilder()
    const target = builder.cut(builder.root)
    const node = builder.ref(builder.root, 'P', relSig([IOTA]))
    builder.wire([
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

    expect(sameDiagram(
      applyDeiteration(
        iterated,
        copySelection,
        evidence.justifier,
        evidence.certificate,
      ),
      diagram,
    )).toBe(true)
  })
})
