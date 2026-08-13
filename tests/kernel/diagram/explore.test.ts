import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagram } from '../../../src/kernel/diagram/diagram'
import {
  exploreForm,
  exploreIso,
  exploreLabeling,
} from '../../../src/kernel/diagram/canonical/explore'
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
    },
    wires: {
      [ids.head]: {
        scope: ids.root,
        sig: relation,
        endpoints: [{ node: ids.atom, port: { kind: 'head' } }],
      },
      [ids.value]: {
        scope: ids.root,
        sig: IOTA,
        endpoints: [
          { node: ids.ref, port: { kind: 'arg', index: 0 } },
          { node: ids.atom, port: { kind: 'arg', index: 0 } },
        ],
      },
    },
  })
}

describe('canonical graph exploration', () => {
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

    expect(exploreForm(first)).toBe(exploreForm(second))
    const iso = exploreIso(first, second)
    expect(iso).not.toBeNull()
    expect(iso?.regions.get('r0')).toBe('sheet')
    expect(iso?.regions.get('r1')).toBe('inside')
  })

  it('returns total distinct ordinals with form equal to exploreForm', () => {
    const diagram = namedGraph({
      root: 'r0',
      cut: 'r1',
      ref: 'ref',
      atom: 'atom',
      value: 'value',
      head: 'head',
    })
    const labeling = exploreLabeling(diagram)

    expect(labeling.form).toBe(exploreForm(diagram))
    expect(new Set(labeling.regionOrd.values()).size).toBe(2)
    expect(new Set(labeling.nodeOrd.values()).size).toBe(2)
    expect(new Set(labeling.wireOrd.values()).size).toBe(2)
  })

  it('distinguishes node content and wire scope', () => {
    const ref = (defId: string) => {
      const builder = new DiagramBuilder()
      builder.ref(builder.root, defId, relSig([]))
      return builder.build()
    }
    expect(exploreForm(ref('P'))).not.toBe(exploreForm(ref('Q')))

    const scoped = (outer: boolean) => {
      const builder = new DiagramBuilder()
      const cut = builder.cut(builder.root)
      const node = builder.ref(cut, 'P', relSig([IOTA]))
      builder.wire( [
        { node, port: { kind: 'arg', index: 0 } },
      ])
      return builder.build()
    }
    expect(exploreForm(scoped(true))).not.toBe(exploreForm(scoped(false)))
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

    expect(exploreForm(diagram, [left, right]))
      .not.toBe(exploreForm(diagram, [right, left]))
    expect(() => exploreForm(diagram, ['ghost'])).toThrowError(/does not exist/)
  })

  it('returns null for non-isomorphic diagrams', () => {
    const unary = new DiagramBuilder()
    unary.ref(unary.root, 'P', relSig([IOTA]))
    const binary = new DiagramBuilder()
    binary.ref(binary.root, 'P', relSig([IOTA, IOTA]))

    expect(exploreIso(unary.build(), binary.build())).toBeNull()
  })
})
