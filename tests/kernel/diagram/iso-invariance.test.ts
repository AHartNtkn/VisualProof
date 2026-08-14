import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagram } from '../../../src/kernel/diagram/diagram'
import {
  diagramIso,
  sameDiagram,
} from '../../../src/kernel/diagram/canonical/iso'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'

function namedGraph(
  ids: {
    root: string
    cut: string
    ref: string
    atom: string
    value: string
    head: string
  },
) {
  const relation = relSig([IOTA])
  return mkDiagram({
    root: ids.root,
    regions: {
      [ids.cut]: { kind: 'cut', parent: ids.root },
      [ids.root]: { kind: 'sheet' },
    },
    nodes: {
      [ids.atom]: { kind: 'atom', region: ids.cut, sig: relation },
      [ids.ref]: { kind: 'ref', region: ids.root, defId: 'P', sig: relation },
      // The head wire's quantifier lives at the root, above the atom's cut.
      [`${ids.head}Pin`]: {
        kind: 'identity',
        region: ids.root,
        sig: relation,
        arity: 1,
      },
    },
    wires: {
      [ids.head]: {
        sig: relation,
        endpoints: [
          { node: ids.atom, port: { kind: 'head' } },
          { node: `${ids.head}Pin`, port: { kind: 'identity', index: 0 } },
        ],
      },
      [ids.value]: {
        sig: IOTA,
        endpoints: [
          { node: ids.ref, port: { kind: 'arg', index: 0 } },
          { node: ids.atom, port: { kind: 'arg', index: 0 } },
        ],
      },
    },
  })
}

describe('diagramIso and sameDiagram invariance', () => {
  it('is invariant under IDs and insertion order', () => {
    const first = namedGraph({
      root: 'r0',
      cut: 'r1',
      ref: 'ref',
      atom: 'atom',
      value: 'value',
      head: 'head',
    })
    const second = namedGraph({
      root: 'sheet',
      cut: 'inside',
      ref: 'z',
      atom: 'a',
      value: 'w9',
      head: 'w0',
    })

    expect(sameDiagram(first, second)).toBe(true)
    const iso = diagramIso(first, second)
    expect(iso).not.toBeNull()
    expect(iso?.regions.get('r0')).toBe('sheet')
    expect(iso?.regions.get('r1')).toBe('inside')
  })

  it('assigns a complete correspondence covering every region, node, and wire', () => {
    const diagram = namedGraph({
      root: 'r0',
      cut: 'r1',
      ref: 'ref',
      atom: 'atom',
      value: 'value',
      head: 'head',
    })
    const renamed = namedGraph({
      root: 'sheet',
      cut: 'inside',
      ref: 'z',
      atom: 'a',
      value: 'w9',
      head: 'w0',
    })
    const iso = diagramIso(diagram, renamed)

    expect(iso).not.toBeNull()
    expect(iso!.regions.size).toBe(2)
    // atom, ref, and the head wire's pin
    expect(iso!.nodes.size).toBe(3)
    expect(iso!.wires.size).toBe(2)
  })

  it('distinguishes node content and wire scope', () => {
    const ref = (defId: string) => {
      const builder = new DiagramBuilder()
      builder.ref(builder.root, defId, relSig([]))
      return builder.build()
    }
    expect(sameDiagram(ref('P'), ref('Q'))).toBe(false)

    const scoped = (outer: boolean) => {
      const builder = new DiagramBuilder()
      const cut = builder.cut(builder.root)
      const node = builder.ref(cut, 'P', relSig([IOTA]))
      const argument = builder.wire([
        { node, port: { kind: 'arg', index: 0 } },
      ])
      builder.pin(argument, outer ? builder.root : cut)
      return builder.build()
    }
    expect(sameDiagram(scoped(true), scoped(false))).toBe(false)
  })

  it('makes ordered boundary pins semantically visible', () => {
    const builder = new DiagramBuilder()
    const ref = builder.ref(builder.root, 'Pair', relSig([IOTA, IOTA]))
    const left = builder.wire( [
      { node: ref, port: { kind: 'arg', index: 0 } },
    ])
    const right = builder.wire( [
      { node: ref, port: { kind: 'arg', index: 1 } },
    ])
    const diagram = builder.build()

    expect(sameDiagram(diagram, diagram, [left, right], [right, left]))
      .toBe(false)
    expect(() => sameDiagram(diagram, diagram, ['ghost'], ['ghost']))
      .toThrowError(/does not exist/)
  })

  it('returns null for non-isomorphic diagrams', () => {
    const unary = new DiagramBuilder()
    unary.ref(unary.root, 'P', relSig([IOTA]))
    const binary = new DiagramBuilder()
    binary.ref(binary.root, 'P', relSig([IOTA, IOTA]))

    expect(diagramIso(unary.build(), binary.build())).toBeNull()
  })
})
