import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { exploreForm } from '../../src/kernel/diagram/canonical/explore'
import { IOTA } from '../../src/kernel/diagram/sig'
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
    const left = builder.wire(builder.root, [])
    const right = builder.wire(builder.root, [])
    const diagram = addIdentity(builder.build(), cut, [left, right])
    const identity = Object.entries(diagram.nodes).find(([, node]) => node.kind === 'identity')
    expect(identity?.[1]).toMatchObject({ kind: 'identity', region: cut, sig: IOTA, arity: 2 })
    expect(diagram.wires[left]!.endpoints).toContainEqual({
      node: identity?.[0],
      port: { kind: 'identity', index: 0 },
    })
    expect(diagram.wires[right]!.endpoints).toContainEqual({
      node: identity?.[0],
      port: { kind: 'identity', index: 1 },
    })
  })

  it('immediately canonicalizes a co-scoped identity into one shared wire', () => {
    const builder = new DiagramBuilder()
    const left = builder.wire(builder.root, [])
    const right = builder.wire(builder.root, [])
    const diagram = addIdentity(builder.build(), builder.root, [right, left])
    expect(Object.values(diagram.nodes).filter((node) => node.kind === 'identity')).toEqual([])
    expect(Object.keys(diagram.wires)).toEqual([left])
    expect(diagram.wires[right]).toBeUndefined()
  })

  it('rejects duplicate, mismatched-signature, and invisible identity wires', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const child = builder.cut(cut)
    const visible = builder.wire(builder.root, [])
    const relation = builder.wire(builder.root, [], UNARY)
    const hidden = builder.wire(child, [])
    const diagram = builder.build()
    expect(() => addIdentity(diagram, cut, [visible])).toThrow(/at least two distinct wires/)
    expect(() => addIdentity(diagram, cut, [visible, visible])).toThrow(/distinct wires/)
    expect(() => addIdentity(diagram, cut, [visible, relation])).toThrow(/same signature/)
    expect(() => addIdentity(diagram, cut, [visible, hidden])).toThrow(/not visible/)
  })

  it('joins and severs ports using exact wire identity', () => {
    const builder = new DiagramBuilder()
    const ref = builder.ref(builder.root, 'UnaryWitness', UNARY)
    const atom = builder.atom(builder.root, UNARY)
    const head = builder.wire(builder.root, [{ node: atom, port: { kind: 'head' } }], UNARY)
    const left = builder.wire(builder.root, [{ node: ref, port: { kind: 'arg', index: 0 } }])
    const right = builder.wire(builder.root, [{ node: atom, port: { kind: 'arg', index: 0 } }])
    const diagram = builder.build()
    const joined = joinPorts(
      diagram,
      { node: ref, port: { kind: 'arg', index: 0 } },
      { node: atom, port: { kind: 'arg', index: 0 } },
    )
    expect(joined.wires[left]!.endpoints).toHaveLength(2)
    expect(joined.wires[right]).toBeUndefined()
    expect(joined.wires[head]).toBeDefined()
    const severed = severEndpoint(joined, left, { node: atom, port: { kind: 'arg', index: 0 } })
    expect(Object.values(severed.wires).filter((wire) => wire.sig.kind === 'iota')).toHaveLength(2)
  })

  it('wraps, reparents, dissolves, and deletes generic graph content', () => {
    const builder = new DiagramBuilder()
    const ref = builder.ref(builder.root, 'UnaryWitness', UNARY)
    const wire = builder.wire(builder.root, [{ node: ref, port: { kind: 'arg', index: 0 } }])
    const diagram = builder.build()
    const selection = mkSelection(diagram, {
      region: diagram.root,
      regions: [],
      nodes: [ref],
      wires: [wire],
    })
    const wrapped = addCut(diagram, selection)
    expect(wrapped.diagram.nodes[ref]!.region).toBe(wrapped.region)
    const moved = reparentNode(wrapped.diagram, ref, wrapped.diagram.root)
    expect(moved.nodes[ref]!.region).toBe(moved.root)
    const dissolved = dissolveRegion(moved, wrapped.region)
    expect(dissolved.regions[wrapped.region]).toBeUndefined()
    expect(deleteHits(dissolved, [{ kind: 'node', id: ref }]).nodes[ref]).toBeUndefined()
  })

  it('uses exact selection deletion and preserves unrelated endpoint-free wires', () => {
    const builder = new DiagramBuilder()
    const doomed = builder.ref(builder.root, 'UnaryWitness', UNARY)
    const privateWire = builder.wire(builder.root, [{ node: doomed, port: { kind: 'arg', index: 0 } }])
    const bare = builder.wire(builder.root, [])
    const diagram = builder.build()
    expect(orphanedWires(diagram, new Set([doomed]))).toEqual([privateWire])
    const selection = mkSelection(diagram, {
      region: diagram.root,
      regions: [],
      nodes: [doomed],
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
    const wire = builder.wire(outer, [{ node: nested, port: { kind: 'arg', index: 0 } }])
    const diagram = builder.build()
    expect(absorbHits(diagram, [
      { kind: 'region', id: outer },
      { kind: 'node', id: nested },
      { kind: 'wire', id: wire },
    ])).toEqual([{ kind: 'region', id: outer }])
  })

  it('joins any homogeneous construction wires deterministically', () => {
    const builder = new DiagramBuilder()
    const first = builder.wire(builder.root, [])
    const second = builder.wire(builder.root, [])
    const joined = joinWires(builder.build(), [second, first])
    expect(Object.keys(joined.wires)).toEqual([first])
  })

  it('rejects heterogeneous endpoint-free wires before mutation', () => {
    const builder = new DiagramBuilder()
    const individual = builder.wire(builder.root, [])
    const relation = builder.wire(builder.root, [], UNARY)
    const diagram = builder.build()
    const before = exploreForm(diagram)

    expect(() => joinWires(diagram, [individual, relation]))
      .toThrow(/same signature/)
    expect(exploreForm(diagram)).toBe(before)
    expect(diagram.wires[individual]).toBeDefined()
    expect(diagram.wires[relation]).toBeDefined()
  })
})
