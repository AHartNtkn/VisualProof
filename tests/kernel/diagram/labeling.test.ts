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
  diagramIso,
  sameDiagram,
} from '../../../src/kernel/diagram/canonical/iso'
import { canonicalWireOrder } from '../../../src/kernel/diagram/canonical/wire-order'
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

describe('canonicalWireOrder and diagramIso correspondence', () => {
  it('provides a canonical wire order and a complete self-correspondence for every sort', () => {
    const diagram = host()
    const iso = diagramIso(diagram, diagram)

    expect(iso).not.toBeNull()
    expect(iso!.regions.size).toBe(Object.keys(diagram.regions).length)
    expect(iso!.nodes.size).toBe(Object.keys(diagram.nodes).length)
    expect(iso!.wires.size).toBe(Object.keys(diagram.wires).length)

    const wireOrder = canonicalWireOrder(diagram)
    expect(wireOrder.size).toBe(Object.keys(diagram.wires).length)
    expect(new Set(wireOrder.values()).size).toBe(wireOrder.size)
  })

  it('assigns a corresponding wire order across a complete id renaming', () => {
    const diagram = host()
    const copy = renamed(diagram)
    const leftWireOrder = canonicalWireOrder(diagram)
    const rightWireOrder = canonicalWireOrder(copy)

    expect(sameDiagram(diagram, copy)).toBe(true)
    for (const [id, ordinal] of leftWireOrder) {
      expect(rightWireOrder.get(`X_${id}`)).toBe(ordinal)
    }
  })
})

describe('diagramIso', () => {
  it('returns the complete identity-like mapping to a renamed graph', () => {
    const diagram = host()
    const copy = renamed(diagram)
    const iso = diagramIso(diagram, copy)

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
    const iso = diagramIso(diagram, copy)!

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
    const iso = diagramIso(left, right)!

    expect(new Set(iso.nodes.values()).size).toBe(2)
    expect(sameDiagram(left, right)).toBe(true)
  })

  it('returns null for non-isomorphic graphs', () => {
    const builder = new DiagramBuilder()
    builder.ref(builder.root, 'Q', relSig([]))
    expect(diagramIso(host(), builder.build())).toBeNull()
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
    const iso = diagramIso(first, second)!

    expect(second.nodes[iso.nodes.get('n0')!]?.region).toBe('r1')
    expect(second.nodes[iso.nodes.get('n1')!]?.region).toBe('r2')
  })

  it('takes a deterministic mapping across a repeated symmetric construction', () => {
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

    expect(sameDiagram(first, second)).toBe(true)
    expect(diagramIso(first, second)).not.toBeNull()
  })
})
