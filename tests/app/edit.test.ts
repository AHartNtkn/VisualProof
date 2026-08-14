import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import type { Diagram, IdentityDiagramNode, NodeId } from '../../src/kernel/diagram/diagram'
import { sameDiagram } from '../../src/kernel/diagram/canonical/iso'
import { diagramFromJson, diagramToJson } from '../../src/kernel/diagram/json'
import { IOTA } from '../../src/kernel/diagram/sig'
import { derivedScope } from '../../src/kernel/diagram/regions'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import {
  absorbHits,
  addCut,
  addIdentity,
  deleteHits,
  deleteSelection,
  dissolveRegion,
  emptyDiagram,
  joinPorts,
  joinWires,
  orphanedWires,
  reparentNode,
  severEndpoint,
} from '../../src/app/edit'
import { UNARY } from '../fixtures/zero-signature'
import { bareWire } from './helpers/build'

function identityNodesOfArity(diagram: Diagram, arity: number): Array<[NodeId, IdentityDiagramNode]> {
  return Object.entries(diagram.nodes)
    .filter((entry): entry is [NodeId, IdentityDiagramNode] =>
      entry[1].kind === 'identity' && entry[1].arity === arity)
}

describe('edit operations (construction mode, mkDiagram-validated surgery)', () => {
  it('starts from the empty sheet', () => {
    const diagram = emptyDiagram()
    expect(diagram).toMatchObject({
      root: 'r0',
      regions: { r0: { kind: 'sheet' } },
      nodes: {},
      wires: {},
    })
  })

  it('places a conditional identity on outer-scoped wires', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const left = bareWire(builder, builder.root)
    const right = bareWire(builder, builder.root)
    const diagram = addIdentity(builder.build(), cut, [left, right])
    const binary = identityNodesOfArity(diagram, 2)
    expect(binary).toHaveLength(1)
    const [identity] = binary[0]!
    expect(diagram.nodes[identity]).toMatchObject({ kind: 'identity', region: cut, sig: IOTA, arity: 2 })
    expect(diagram.wires[left]!.endpoints).toContainEqual({
      node: identity,
      port: { kind: 'identity', index: 0 },
    })
    expect(diagram.wires[right]!.endpoints).toContainEqual({
      node: identity,
      port: { kind: 'identity', index: 1 },
    })
    // The identity sits under the wires' pins, so it does not move either
    // quantifier: both still read at the sheet.
    expect(derivedScope(diagram, left)).toBe(diagram.root)
    expect(derivedScope(diagram, right)).toBe(diagram.root)
  })

  it('leaves a co-scoped identity as a node — merging wires is joinWires, not addIdentity', () => {
    const builder = new DiagramBuilder()
    const left = bareWire(builder, builder.root)
    const right = bareWire(builder, builder.root)
    const diagram = addIdentity(builder.build(), builder.root, [right, left])
    // Construction never rewrites the picture behind the author's back: the
    // two wires stay two, equated by the node they now share.
    expect(Object.keys(diagram.wires).sort()).toEqual([left, right].sort())
    expect(identityNodesOfArity(diagram, 2)).toHaveLength(1)

    const merged = joinWires(diagram, [left, right])
    expect(Object.keys(merged.wires)).toEqual([left])
  })

  it('pins a single wire, and refuses a point with no signature to give it', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const wire = bareWire(builder, builder.root)
    const diagram = builder.build()

    const pinned = addIdentity(diagram, cut, [wire])
    const unary = identityNodesOfArity(pinned, 1)
      .filter(([, node]) => node.region === cut)
    expect(unary).toHaveLength(1)
    expect(pinned.wires[wire]!.endpoints).toHaveLength(3)

    expect(() => addIdentity(diagram, cut, [])).toThrow(/needs an explicit signature/)
    const point = addIdentity(diagram, cut, [], IOTA)
    expect(identityNodesOfArity(point, 0)).toHaveLength(1)
  })

  it('rejects duplicate, mismatched-signature, and invisible identity wires', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const child = builder.cut(cut)
    const visible = bareWire(builder, builder.root)
    const relation = bareWire(builder, builder.root, UNARY)
    const hidden = bareWire(builder, child)
    const diagram = builder.build()
    expect(() => addIdentity(diagram, cut, [visible, visible])).toThrow(/distinct wires/)
    expect(() => addIdentity(diagram, cut, [visible, relation])).toThrow(/same signature/)
    expect(() => addIdentity(diagram, cut, [visible, hidden])).toThrow(/not visible/)
  })

  it('joins and severs ports using exact wire identity', () => {
    const builder = new DiagramBuilder()
    const ref = builder.ref(builder.root, 'UnaryWitness', UNARY)
    const atom = builder.atom(builder.root, UNARY)
    const head = builder.wire([{ node: atom, port: { kind: 'head' } }], UNARY)
    const left = builder.wire([{ node: ref, port: { kind: 'arg', index: 0 } }])
    const right = builder.wire([{ node: atom, port: { kind: 'arg', index: 0 } }])
    const diagram = builder.build()
    const joined = joinPorts(
      diagram,
      { node: ref, port: { kind: 'arg', index: 0 } },
      { node: atom, port: { kind: 'arg', index: 0 } },
    )
    // Both argument ports plus the two pins the builder gave the open ends.
    expect(joined.wires[left]!.endpoints).toHaveLength(4)
    expect(joined.wires[left]!.endpoints).toContainEqual({ node: ref, port: { kind: 'arg', index: 0 } })
    expect(joined.wires[left]!.endpoints).toContainEqual({ node: atom, port: { kind: 'arg', index: 0 } })
    expect(joined.wires[right]).toBeUndefined()
    expect(joined.wires[head]).toBeDefined()
    const severed = severEndpoint(joined, left, { node: atom, port: { kind: 'arg', index: 0 } })
    expect(Object.values(severed.wires).filter((wire) => wire.sig.kind === 'iota')).toHaveLength(2)
    for (const [id, wire] of Object.entries(severed.wires)) {
      if (wire.sig.kind !== 'iota') continue
      expect(derivedScope(severed, id)).toBe(severed.root)
    }
  })

  it('wraps, reparents, dissolves, and deletes generic graph content', () => {
    const builder = new DiagramBuilder()
    const ref = builder.ref(builder.root, 'UnaryWitness', UNARY)
    const wire = builder.wire([{ node: ref, port: { kind: 'arg', index: 0 } }])
    const pin = builder.pin(wire, builder.root)
    const diagram = builder.build()
    const selection = mkSelection(diagram, {
      region: diagram.root,
      regions: [],
      nodes: [ref, pin],
      wires: [wire],
    })
    const wrapped = addCut(diagram, selection)
    expect(wrapped.diagram.nodes[ref]!.region).toBe(wrapped.region)
    expect(derivedScope(wrapped.diagram, wire)).toBe(wrapped.region)
    const moved = reparentNode(wrapped.diagram, ref, wrapped.diagram.root)
    expect(moved.nodes[ref]!.region).toBe(moved.root)
    const dissolved = dissolveRegion(moved, wrapped.region)
    expect(dissolved.regions[wrapped.region]).toBeUndefined()
    expect(deleteHits(dissolved, [{ kind: 'node', id: ref }]).nodes[ref]).toBeUndefined()
  })

  it('uses exact selection deletion and preserves unrelated bare wires', () => {
    const builder = new DiagramBuilder()
    const doomed = builder.ref(builder.root, 'UnaryWitness', UNARY)
    const privateWire = builder.wire([{ node: doomed, port: { kind: 'arg', index: 0 } }])
    const privatePin = builder.pin(privateWire, builder.root)
    const bare = bareWire(builder, builder.root)
    const diagram = builder.build()
    expect(orphanedWires(diagram, new Set([doomed, privatePin]))).toEqual([privateWire])
    const selection = mkSelection(diagram, {
      region: diagram.root,
      regions: [],
      nodes: [doomed, privatePin],
      wires: [privateWire],
    })
    const deleted = deleteSelection(diagram, selection)
    expect(deleted.nodes[doomed]).toBeUndefined()
    expect(deleted.wires[privateWire]).toBeUndefined()
    expect(deleted.wires[bare]).toBeDefined()
  })

  it('absorbs hits already represented by a selected subtree', () => {
    const builder = new DiagramBuilder()
    const outer = builder.cut(builder.root)
    const nested = builder.ref(outer, 'UnaryWitness', UNARY)
    const wire = builder.wire([{ node: nested, port: { kind: 'arg', index: 0 } }])
    builder.pin(wire, outer)
    const diagram = builder.build()
    expect(absorbHits(diagram, [
      { kind: 'region', id: outer },
      { kind: 'node', id: nested },
      { kind: 'wire', id: wire },
    ])).toEqual([{ kind: 'region', id: outer }])
  })

  it('joins any homogeneous construction wires deterministically', () => {
    const builder = new DiagramBuilder()
    const first = bareWire(builder, builder.root)
    const second = bareWire(builder, builder.root)
    const joined = joinWires(builder.build(), [second, first])
    expect(Object.keys(joined.wires)).toEqual([first])
    expect(joined.wires[first]!.endpoints).toHaveLength(4)
  })

  it('rejects heterogeneous bare wires before mutation', () => {
    const builder = new DiagramBuilder()
    const individual = bareWire(builder, builder.root)
    const relation = bareWire(builder, builder.root, UNARY)
    const diagram = builder.build()
    const before = diagramFromJson(diagramToJson(diagram))

    expect(() => joinWires(diagram, [individual, relation]))
      .toThrow(/same signature/)
    expect(sameDiagram(diagram, before)).toBe(true)
    expect(diagram.wires[individual]).toBeDefined()
    expect(diagram.wires[relation]).toBeDefined()
  })
})
