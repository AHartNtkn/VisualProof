import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import type {
  Diagram,
  DiagramNode,
  Endpoint,
  Region,
  Wire,
} from '../../../src/kernel/diagram/diagram'
import { mkDiagram } from '../../../src/kernel/diagram/diagram'
import {
  exploreForm,
  exploreIso,
  exploreLabeling,
} from '../../../src/kernel/diagram/canonical/explore'
import { derivedScope } from '../../../src/kernel/diagram/regions'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'

/**
 * A closed diagram spanning every node kind and both derived scopes: `value`
 * reaches out of the cut to the ref, while `head` and `other` stay inside it.
 * The pins are the second ends the otherwise one-ended wires need.
 */
function host(): Diagram {
  const relation = relSig([IOTA])
  return mkDiagram({
    root: 'r0',
    regions: {
      r0: { kind: 'sheet' },
      r1: { kind: 'cut', parent: 'r0' },
    },
    nodes: {
      atom: { kind: 'atom', region: 'r1', sig: relation },
      ref: { kind: 'ref', region: 'r0', defId: 'P', sig: relation },
      identity: { kind: 'identity', region: 'r1', sig: IOTA, arity: 2 },
      headpin: { kind: 'identity', region: 'r1', sig: relation, arity: 1 },
      otherpin: { kind: 'identity', region: 'r1', sig: IOTA, arity: 1 },
    },
    wires: {
      head: {
        sig: relation,
        endpoints: [
          { node: 'atom', port: { kind: 'head' } },
          { node: 'headpin', port: { kind: 'identity', index: 0 } },
        ],
      },
      value: {
        sig: IOTA,
        endpoints: [
          { node: 'atom', port: { kind: 'arg', index: 0 } },
          { node: 'ref', port: { kind: 'arg', index: 0 } },
          { node: 'identity', port: { kind: 'identity', index: 0 } },
        ],
      },
      other: {
        sig: IOTA,
        endpoints: [
          { node: 'identity', port: { kind: 'identity', index: 1 } },
          { node: 'otherpin', port: { kind: 'identity', index: 0 } },
        ],
      },
    },
  })
}

function renamed(diagram: Diagram): Diagram {
  const rename = (id: string) => `X_${id}`
  const regions: Record<string, Region> = {}
  for (const [id, region] of Object.entries(diagram.regions)) {
    regions[rename(id)] = region.kind === 'sheet'
      ? region
      : { kind: 'cut', parent: rename(region.parent) }
  }
  const nodes: Record<string, DiagramNode> = {}
  for (const [id, node] of Object.entries(diagram.nodes)) {
    switch (node.kind) {
      case 'atom':
        nodes[rename(id)] = {
          kind: 'atom',
          region: rename(node.region),
          sig: node.sig,
        }
        break
      case 'ref':
        nodes[rename(id)] = {
          kind: 'ref',
          region: rename(node.region),
          defId: node.defId,
          sig: node.sig,
        }
        break
      case 'identity':
        nodes[rename(id)] = {
          kind: 'identity',
          region: rename(node.region),
          sig: node.sig,
          arity: node.arity,
        }
        break
    }
  }
  const wires: Record<string, Wire> = {}
  for (const [id, wire] of Object.entries(diagram.wires)) {
    wires[rename(id)] = {
      sig: wire.sig,
      endpoints: wire.endpoints.map((endpoint) => ({
        node: rename(endpoint.node),
        port: endpoint.port,
      })),
    }
  }
  return mkDiagram({
    root: rename(diagram.root),
    regions,
    nodes,
    wires,
  })
}

function semanticEndpointKey(diagram: Diagram, endpoint: Endpoint): string {
  const node = diagram.nodes[endpoint.node]!
  const position = node.kind === 'identity'
    ? 'identity'
    : endpoint.port.kind === 'head'
      ? 'head'
      : endpoint.port.kind === 'arg'
        ? `arg:${endpoint.port.index}`
        : 'invalid'
  return JSON.stringify([endpoint.node, position])
}

describe('exploreLabeling', () => {
  it('returns exploreForm and total distinct ordinals for every sort', () => {
    const diagram = host()
    const labeling = exploreLabeling(diagram)

    expect(labeling.form).toBe(exploreForm(diagram))
    expect(labeling.regionOrd.size).toBe(Object.keys(diagram.regions).length)
    expect(labeling.nodeOrd.size).toBe(Object.keys(diagram.nodes).length)
    expect(labeling.wireOrd.size).toBe(Object.keys(diagram.wires).length)
    expect(new Set(labeling.regionOrd.values()).size).toBe(labeling.regionOrd.size)
    expect(new Set(labeling.nodeOrd.values()).size).toBe(labeling.nodeOrd.size)
    expect(new Set(labeling.wireOrd.values()).size).toBe(labeling.wireOrd.size)
  })

  it('assigns corresponding ordinals across a complete id renaming', () => {
    const diagram = host()
    const copy = renamed(diagram)
    const left = exploreLabeling(diagram)
    const right = exploreLabeling(copy)

    expect(left.form).toBe(right.form)
    for (const [id, ordinal] of left.regionOrd) {
      expect(right.regionOrd.get(`X_${id}`)).toBe(ordinal)
    }
    for (const [id, ordinal] of left.nodeOrd) {
      expect(right.nodeOrd.get(`X_${id}`)).toBe(ordinal)
    }
    for (const [id, ordinal] of left.wireOrd) {
      expect(right.wireOrd.get(`X_${id}`)).toBe(ordinal)
    }
  })
})

describe('exploreIso', () => {
  it('returns the complete identity-like mapping to a renamed graph', () => {
    const diagram = host()
    const copy = renamed(diagram)
    const iso = exploreIso(diagram, copy)

    expect(iso).not.toBeNull()
    for (const id of Object.keys(diagram.regions)) {
      expect(iso!.regions.get(id)).toBe(`X_${id}`)
    }
    for (const id of Object.keys(diagram.nodes)) {
      expect(iso!.nodes.get(id)).toBe(`X_${id}`)
    }
    for (const id of Object.keys(diagram.wires)) {
      expect(iso!.wires.get(id)).toBe(`X_${id}`)
    }
  })

  it('transports parents, node regions, wire scopes, and endpoint multisets', () => {
    const diagram = host()
    const copy = renamed(diagram)
    const iso = exploreIso(diagram, copy)!

    for (const [id, region] of Object.entries(diagram.regions)) {
      const image = copy.regions[iso.regions.get(id)!]!
      if (region.kind === 'sheet') {
        expect(image.kind).toBe('sheet')
      } else {
        expect(image).toEqual({
          kind: 'cut',
          parent: iso.regions.get(region.parent),
        })
      }
    }
    for (const [id, node] of Object.entries(diagram.nodes)) {
      expect(copy.nodes[iso.nodes.get(id)!]?.region)
        .toBe(iso.regions.get(node.region))
    }
    for (const [id, wire] of Object.entries(diagram.wires)) {
      const image = copy.wires[iso.wires.get(id)!]!
      expect(derivedScope(copy, iso.wires.get(id)!))
        .toBe(iso.regions.get(derivedScope(diagram, id)))
      const expected = wire.endpoints.map((endpoint) =>
        semanticEndpointKey(copy, {
          node: iso.nodes.get(endpoint.node)!,
          port: endpoint.port,
        }),
      ).sort()
      expect(image.endpoints.map((endpoint) =>
        semanticEndpointKey(copy, endpoint),
      ).sort()).toEqual(expected)
    }
  })

  it('picks a bijective map for a symmetric graph', () => {
    const make = () => {
      const builder = new DiagramBuilder()
      builder.ref(builder.root, 'P', relSig([]))
      builder.ref(builder.root, 'P', relSig([]))
      return builder.build()
    }
    const left = make()
    const right = make()
    const iso = exploreIso(left, right)!

    expect(new Set(iso.nodes.values()).size).toBe(2)
    expect(exploreForm(left)).toBe(exploreForm(right))
  })

  it('returns null for non-isomorphic graphs', () => {
    const builder = new DiagramBuilder()
    builder.ref(builder.root, 'Q', relSig([]))
    expect(exploreIso(host(), builder.build())).toBeNull()
  })

  it('uses winning structural colors rather than insertion order', () => {
    const first = mkDiagram({
      root: 'r0',
      regions: {
        r0: { kind: 'sheet' },
        r1: { kind: 'cut', parent: 'r0' },
        r2: { kind: 'cut', parent: 'r1' },
      },
      nodes: {
        n0: { kind: 'ref', region: 'r1', defId: 'P', sig: relSig([]) },
        n1: { kind: 'ref', region: 'r2', defId: 'P', sig: relSig([]) },
      },
      wires: {},
    })
    const second = mkDiagram({
      root: 'r0',
      regions: {
        r0: { kind: 'sheet' },
        r1: { kind: 'cut', parent: 'r0' },
        r2: { kind: 'cut', parent: 'r1' },
      },
      nodes: {
        n0: { kind: 'ref', region: 'r2', defId: 'P', sig: relSig([]) },
        n1: { kind: 'ref', region: 'r1', defId: 'P', sig: relSig([]) },
      },
      wires: {},
    })
    const iso = exploreIso(first, second)!

    expect(second.nodes[iso.nodes.get('n0')!]?.region).toBe('r1')
    expect(second.nodes[iso.nodes.get('n1')!]?.region).toBe('r2')
  })

  it('takes a deterministic lexicographically minimal symmetry branch', () => {
    const make = () => {
      const builder = new DiagramBuilder()
      const outer = builder.cut(builder.root)
      const inner = builder.cut(outer)
      builder.ref(outer, 'P', relSig([]))
      builder.ref(inner, 'P', relSig([]))
      return builder.build()
    }
    const first = make()
    const second = make()

    expect(exploreForm(first)).toBe(exploreForm(second))
    expect(exploreIso(first, second)).not.toBeNull()
  })
})
