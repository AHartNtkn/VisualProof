import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import {
  absorbHits,
  addCut,
  addBubble,
  deleteHits,
  deleteSelection,
  dissolveRegion,
  emptyDiagram,
  joinPorts,
  joinWires,
  orphanedWires,
  reparentNode,
  severEndpoint,
} from '../../src/interaction/edit'
import { spawnBoundRelationNode, spawnRelationNode, spawnTermNode } from '../../src/kernel/diagram/spawn'

const p = (s: string) => parseTerm(s)

describe('edit operations (construction mode, mkDiagram-validated surgery)', () => {
  it('starts from the empty sheet and adds parsed term nodes with auto wires', () => {
    const d0 = emptyDiagram()
    expect(Object.keys(d0.nodes)).toHaveLength(0)
    const { diagram: d1, node } = spawnTermNode(d0, d0.root, p('\\x. x y'))
    expect(d1.nodes[node]?.kind).toBe('term')
    // output + y singleton wires materialized
    const touching = Object.values(d1.wires).filter((w) => w.endpoints.some((ep) => ep.node === node))
    expect(touching).toHaveLength(2)
  })

  it('adds an atom bound to an enclosing bubble with one scoped singleton wire per derived argument', () => {
    const b = new DiagramBuilder()
    const bubble = b.bubble(b.root, 2)
    const cut = b.cut(bubble)
    const d = b.build()

    const { diagram, node } = spawnBoundRelationNode(d, cut, bubble)

    expect(diagram.nodes[node]).toEqual({ kind: 'atom', region: cut, binder: bubble })
    expect(Object.values(diagram.wires).filter((wire) =>
      wire.endpoints.some((endpoint) => endpoint.node === node),
    )).toEqual([
      { scope: cut, endpoints: [{ node, port: { kind: 'arg', index: 0 } }] },
      { scope: cut, endpoints: [{ node, port: { kind: 'arg', index: 1 } }] },
    ])
  })

  it('rejects an atom whose chosen bubble does not enclose the invocation region', () => {
    const b = new DiagramBuilder()
    const left = b.bubble(b.root, 1)
    const right = b.cut(b.root)
    const d = b.build()

    expect(() => spawnBoundRelationNode(d, right, left)).toThrow(/must lie inside its binder bubble/)
  })

  it('wraps a selection in a single cut and in a bubble', () => {
    const d0 = emptyDiagram()
    const { diagram: d1, node } = spawnTermNode(d0, d0.root, p('y'))
    const sel = mkSelection(d1, { region: d1.root, regions: [], nodes: [node], wires: [] })
    const { diagram: d2, region: cut } = addCut(d1, sel)
    expect(d2.regions[cut]?.kind).toBe('cut')
    expect(d2.nodes[node]?.region).toBe(cut)
    const sel2 = mkSelection(d2, { region: d2.root, regions: [cut], nodes: [], wires: [] })
    const { diagram: d3, region: bub } = addBubble(d2, sel2, 2)
    expect(d3.regions[bub]?.kind).toBe('bubble')
    expect((d3.regions[cut] as { parent: string }).parent).toBe(bub)
  })

  it('joins two ports onto one wire (construction-level identification)', () => {
    const d0 = emptyDiagram()
    const a = spawnTermNode(d0, d0.root, p('\\x. x'))
    const b = spawnTermNode(a.diagram, a.diagram.root, p('y'))
    const d = b.diagram
    const out = joinPorts(d,
      { node: a.node, port: { kind: 'output' } },
      { node: b.node, port: { kind: 'freeVar', name: 's0' } })
    const shared = Object.values(out.wires).find((w) =>
      w.endpoints.some((ep) => ep.node === a.node) && w.endpoints.some((ep) => ep.node === b.node))
    expect(shared).toBeDefined()
    expect(shared!.endpoints).toHaveLength(2)
  })

  it('joinPorts merges the wires at their deepest common scope', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const n1 = h.termNode(cut, p('\\x. x'))
    const n2 = h.termNode(h.root, p('y'))
    const d = h.build()
    const out = joinPorts(d,
      { node: n1, port: { kind: 'output' } },
      { node: n2, port: { kind: 'freeVar', name: 's0' } })
    const shared = Object.values(out.wires).find((w) => w.endpoints.length === 2)!
    expect(shared.scope).toBe(d.root)
  })

  it('joinPorts scopes across incomparable regions at the deepest common ancestor, not the root', () => {
    const h = new DiagramBuilder()
    const outer = h.cut(h.root)
    const left = h.cut(outer)
    const right = h.cut(outer)
    const n1 = h.termNode(left, p('\\x. x'))
    const n2 = h.termNode(right, p('y'))
    const d = h.build()
    const out = joinPorts(d,
      { node: n1, port: { kind: 'output' } },
      { node: n2, port: { kind: 'freeVar', name: 's0' } })
    const shared = Object.values(out.wires).find((w) => w.endpoints.length === 2)!
    expect(shared.scope).toBe(outer)
  })

  it('deletes a selection, trimming touching wires', () => {
    const d0 = emptyDiagram()
    const a = spawnTermNode(d0, d0.root, p('\\x. x'))
    const b = spawnTermNode(a.diagram, a.diagram.root, p('y'))
    const joined = joinPorts(b.diagram,
      { node: a.node, port: { kind: 'output' } },
      { node: b.node, port: { kind: 'freeVar', name: 's0' } })
    const sel = mkSelection(joined, { region: joined.root, regions: [], nodes: [b.node], wires: [] })
    const out = deleteSelection(joined, sel)
    expect(out.nodes[b.node]).toBeUndefined()
    expect(out.nodes[a.node]).toBeDefined()
  })

  it('refuses a pre-canonical port spelling, naming the canonical ports', () => {
    // construction canonicalized the term's free 'y' to 's0'; an endpoint
    // still spelling 'y' is invalid input, rejected against the node's
    // CURRENT term rather than reported as a missing wire
    const d0 = emptyDiagram()
    const a = spawnTermNode(d0, d0.root, p('\\x. x'))
    const b = spawnTermNode(a.diagram, a.diagram.root, p('y'))
    expect(() => joinPorts(b.diagram,
      { node: a.node, port: { kind: 'output' } },
      { node: b.node, port: { kind: 'freeVar', name: 'y' } }))
      .toThrowError(/has no port 'v:y' \(its ports are out, v:s0/)
  })

  it('refuses joining a port to itself, loudly', () => {
    const d0 = emptyDiagram()
    const a = spawnTermNode(d0, d0.root, p('\\x. x'))
    expect(() => joinPorts(a.diagram,
      { node: a.node, port: { kind: 'output' } },
      { node: a.node, port: { kind: 'output' } })).toThrowError(/same port/)
  })
})

describe('spawnRelationNode', () => {
  it('spawns a ref node with one fresh bare-ended wire per argument, in the chosen region', () => {
    const d0 = emptyDiagram()
    const { diagram, node } = spawnRelationNode(d0, d0.root, 'plus', 3)
    const n = diagram.nodes[node]!
    expect(n.kind).toBe('ref')
    if (n.kind === 'ref') {
      expect(n.defId).toBe('plus')
      expect(n.arity).toBe(3)
    }
    // three wires, each holding exactly the ref's arg endpoint i
    const wires = Object.values(diagram.wires)
    expect(wires).toHaveLength(3)
    const indices = wires.map((w) => {
      expect(w.endpoints).toHaveLength(1)
      expect(w.endpoints[0]!.node).toBe(node)
      expect(w.scope).toBe(d0.root)
      const port = w.endpoints[0]!.port
      if (port.kind !== 'arg') throw new Error(`expected arg port, got ${port.kind}`)
      return port.index
    }).sort()
    expect(indices).toEqual([0, 1, 2])
  })

  it('does not disturb existing content', () => {
    const d0 = emptyDiagram()
    const { diagram: d1, node: t } = spawnTermNode(d0, d0.root, parseTerm('\\x. x'))
    const { diagram: d2 } = spawnRelationNode(d1, d1.root, 'r', 1)
    expect(d2.nodes[t]).toEqual(d1.nodes[t])
  })

  it('spawns terms and exact qualified refs with every fresh wire in the chosen nested region', () => {
    const b = new DiagramBuilder()
    const cut = b.cut(b.root)
    const start = b.build()
    const term = spawnTermNode(start, cut, p('x'))
    const ref = spawnRelationNode(term.diagram, cut, 'arith/reallyLongRelation', 2)

    expect(ref.diagram.nodes[term.node]?.region).toBe(cut)
    expect(ref.diagram.nodes[ref.node]).toMatchObject({ kind: 'ref', region: cut, defId: 'arith/reallyLongRelation', arity: 2 })
    for (const wire of Object.values(ref.diagram.wires)) expect(wire.scope).toBe(cut)
  })
})

describe('wire construction primitives', () => {
  it('joins endpointful and endpointless wires n-arily at their DCA with a deterministic survivor', () => {
    const b = new DiagramBuilder()
    const outer = b.cut(b.root)
    const left = b.cut(outer)
    const right = b.cut(outer)
    const l = b.ref(left, 'L', 1)
    const r = b.ref(right, 'R', 1)
    const wl = b.wire(left, [{ node: l, port: { kind: 'arg', index: 0 } }])
    const wr = b.wire(right, [{ node: r, port: { kind: 'arg', index: 0 } }])
    const bare = b.wire(right, [])
    const d = b.build()
    const ids = [wl, wr, bare].sort()

    const out = joinWires(d, [wr, bare, wl])
    expect(Object.keys(out.wires)).toEqual([ids[0]])
    expect(out.wires[ids[0]!]!.scope).toBe(outer)
    expect(out.wires[ids[0]!]!.endpoints.map((endpoint) => endpoint.node).sort()).toEqual([l, r].sort())
    expect(joinWires(d, [wl, wr, bare])).toEqual(out)
  })

  it('joins two endpointless wires and refuses incomplete, duplicate, or unknown requests', () => {
    const b = new DiagramBuilder()
    const cut = b.cut(b.root)
    const rootBare = b.wire(b.root, [])
    const cutBare = b.wire(cut, [])
    const d = b.build()
    const survivor = [rootBare, cutBare].sort()[0]!
    const out = joinWires(d, [cutBare, rootBare])
    expect(Object.keys(out.wires)).toEqual([survivor])
    expect(out.wires[survivor]).toEqual({ scope: d.root, endpoints: [] })
    expect(() => joinWires(d, [rootBare])).toThrow(/at least two wires/)
    expect(() => joinWires(d, [rootBare, rootBare])).toThrow(/more than once/)
    expect(() => joinWires(d, [rootBare, 'ghost'])).toThrow(/unknown wire 'ghost'/)
  })

  it('severs one endpoint onto a fresh singleton and preserves both scopes', () => {
    const b = new DiagramBuilder()
    const cut = b.cut(b.root)
    const a = b.ref(cut, 'A', 1)
    const c = b.ref(cut, 'B', 1)
    const wire = b.wire(cut, [
      { node: a, port: { kind: 'arg', index: 0 } },
      { node: c, port: { kind: 'arg', index: 0 } },
    ])
    const d = b.build()
    const out = severEndpoint(d, wire, { node: c, port: { kind: 'arg', index: 0 } })
    const fresh = Object.keys(out.wires).find((id) => id !== wire)!
    expect(out.wires[wire]).toEqual({ scope: cut, endpoints: [{ node: a, port: { kind: 'arg', index: 0 } }] })
    expect(out.wires[fresh]).toEqual({ scope: cut, endpoints: [{ node: c, port: { kind: 'arg', index: 0 } }] })
    expect(() => severEndpoint(out, fresh, out.wires[fresh]!.endpoints[0]!)).toThrow(/single loose end/)
    expect(() => severEndpoint(d, wire, { node: a, port: { kind: 'arg', index: 9 } })).toThrow(/not on wire/)
  })
})

describe('construction wrapping', () => {
  it('makes a new bubble the binder of directly wrapped predicate atoms', () => {
    const b = new DiagramBuilder()
    const oldBinder = b.bubble(b.root, 1)
    const atom = b.atom(oldBinder, oldBinder)
    const d = b.build()
    const selection = mkSelection(d, { region: oldBinder, regions: [], nodes: [atom], wires: [] })
    const { diagram, region } = addBubble(d, selection, 1)
    expect(diagram.nodes[atom]).toEqual({ kind: 'atom', region, binder: region })
  })

  it('preserves inner binder identity when an existing bubble subtree is wrapped', () => {
    const b = new DiagramBuilder()
    const inner = b.bubble(b.root, 1)
    const atom = b.atom(inner, inner)
    const d = b.build()
    const selection = mkSelection(d, { region: d.root, regions: [inner], nodes: [], wires: [] })
    const { diagram, region: outer } = addBubble(d, selection, 1)
    expect(diagram.nodes[atom]).toEqual({ kind: 'atom', region: inner, binder: inner })
    expect(diagram.regions[inner]).toEqual({ kind: 'bubble', parent: outer, arity: 1 })
  })

  it('moves wholly enclosed endpointful wires and an explicitly selected bare wire, but not crossing or unrelated bare wires', () => {
    const b = new DiagramBuilder()
    const inside = b.termNode(b.root, p('x'))
    const outside = b.termNode(b.root, p('y'))
    const privateWire = b.wire(b.root, [{ node: inside, port: { kind: 'output' } }])
    const crossing = b.wire(b.root, [
      { node: inside, port: { kind: 'freeVar', name: 'x' } },
      { node: outside, port: { kind: 'freeVar', name: 'y' } },
    ])
    const selectedBare = b.wire(b.root, [])
    const unrelatedBare = b.wire(b.root, [])
    const d = b.build()
    const selection = mkSelection(d, { region: d.root, regions: [], nodes: [inside], wires: [selectedBare] })
    const { diagram, region } = addCut(d, selection)

    expect(diagram.nodes[inside]?.region).toBe(region)
    expect(diagram.nodes[outside]?.region).toBe(d.root)
    expect(diagram.wires[privateWire]?.scope).toBe(region)
    expect(diagram.wires[selectedBare]?.scope).toBe(region)
    expect(diagram.wires[crossing]?.scope).toBe(d.root)
    expect(diagram.wires[unrelatedBare]?.scope).toBe(d.root)
  })

  it('moves a parent-scoped wire whose endpoints lie in a selected child subtree', () => {
    const b = new DiagramBuilder()
    const cut = b.cut(b.root)
    const node = b.ref(cut, 'P', 1)
    const enclosed = b.wire(b.root, [{ node, port: { kind: 'arg', index: 0 } }])
    const d = b.build()
    const selection = mkSelection(d, { region: d.root, regions: [cut], nodes: [], wires: [] })
    const { diagram, region } = addBubble(d, selection, 0)
    expect((diagram.regions[cut] as { parent: string }).parent).toBe(region)
    expect(diagram.wires[enclosed]?.scope).toBe(region)
  })

  it('absorb-normalizes selected subtrees without swallowing parent-scoped touching wires', () => {
    const b = new DiagramBuilder()
    const outer = b.cut(b.root)
    const inner = b.cut(outer)
    const nested = b.ref(inner, 'nested', 2)
    const rootNode = b.ref(b.root, 'root', 1)
    const internal = b.wire(inner, [{ node: nested, port: { kind: 'arg', index: 0 } }])
    const touching = b.wire(b.root, [
      { node: nested, port: { kind: 'arg', index: 1 } },
      { node: rootNode, port: { kind: 'arg', index: 0 } },
    ])
    const d = b.build()
    expect(absorbHits(d, [
      { kind: 'region', id: outer },
      { kind: 'region', id: inner },
      { kind: 'node', id: nested },
      { kind: 'wire', id: internal },
      { kind: 'wire', id: touching },
      { kind: 'region', id: outer },
    ])).toEqual([
      { kind: 'region', id: outer },
      { kind: 'wire', id: touching },
    ])
  })
})

describe('construction deletion and dissolution', () => {
  it('dissolves a boundary and promotes its direct contents, child regions, and scoped wires', () => {
    const b = new DiagramBuilder()
    const outer = b.cut(b.root)
    const child = b.cut(outer)
    const direct = b.ref(outer, 'direct', 1)
    const nested = b.ref(child, 'nested', 1)
    const directWire = b.wire(outer, [{ node: direct, port: { kind: 'arg', index: 0 } }])
    const nestedWire = b.wire(child, [{ node: nested, port: { kind: 'arg', index: 0 } }])
    const d = b.build()
    const out = dissolveRegion(d, outer)
    expect(out.regions[outer]).toBeUndefined()
    expect((out.regions[child] as { parent: string }).parent).toBe(d.root)
    expect(out.nodes[direct]?.region).toBe(d.root)
    expect(out.nodes[nested]?.region).toBe(child)
    expect(out.wires[directWire]?.scope).toBe(d.root)
    expect(out.wires[nestedWire]?.scope).toBe(child)
  })

  it('dissolving a bubble removes its binder-dependent atoms and their orphaned endpoints', () => {
    const b = new DiagramBuilder()
    const bubble = b.bubble(b.root, 2)
    const atom = b.atom(bubble, bubble)
    const survivor = b.ref(b.root, 'survivor', 1)
    const privateWire = b.wire(bubble, [{ node: atom, port: { kind: 'arg', index: 0 } }])
    const sharedWire = b.wire(b.root, [
      { node: atom, port: { kind: 'arg', index: 1 } },
      { node: survivor, port: { kind: 'arg', index: 0 } },
    ])
    const out = deleteHits(b.build(), [{ kind: 'region', id: bubble }])
    expect(out.regions[bubble]).toBeUndefined()
    expect(out.nodes[atom]).toBeUndefined()
    expect(out.nodes[survivor]).toBeDefined()
    expect(out.wires[privateWire]).toBeUndefined()
    expect(out.wires[sharedWire]?.endpoints).toEqual([{ node: survivor, port: { kind: 'arg', index: 0 } }])
  })

  it('deletes node-only wires, trims shared wires, and retains unrelated pre-existing bare wires', () => {
    const b = new DiagramBuilder()
    const cut = b.cut(b.root)
    const doomed = b.ref(cut, 'doomed', 2)
    const survivor = b.ref(b.root, 'survivor', 1)
    const privateWire = b.wire(cut, [{ node: doomed, port: { kind: 'arg', index: 0 } }])
    const sharedWire = b.wire(b.root, [
      { node: doomed, port: { kind: 'arg', index: 1 } },
      { node: survivor, port: { kind: 'arg', index: 0 } },
    ])
    const bare = b.wire(b.root, [])
    const d = b.build()
    expect(orphanedWires(d, new Set([doomed]))).toEqual([privateWire])
    const out = deleteHits(d, [{ kind: 'node', id: doomed }])
    expect(out.nodes[doomed]).toBeUndefined()
    expect(out.nodes[survivor]).toBeDefined()
    expect(out.wires[privateWire]).toBeUndefined()
    expect(out.wires[sharedWire]?.endpoints).toEqual([{ node: survivor, port: { kind: 'arg', index: 0 } }])
    expect(out.wires[bare]).toEqual({ scope: d.root, endpoints: [] })
  })

  it('deletes nodes across anchors and takes a shared wire when all of its endpoints die', () => {
    const b = new DiagramBuilder()
    const left = b.cut(b.root)
    const right = b.cut(b.root)
    const a = b.ref(left, 'A', 1)
    const z = b.ref(right, 'Z', 1)
    const shared = b.wire(b.root, [
      { node: a, port: { kind: 'arg', index: 0 } },
      { node: z, port: { kind: 'arg', index: 0 } },
    ])
    const d = b.build()
    const out = deleteHits(d, [{ kind: 'node', id: a }, { kind: 'node', id: z }])
    expect(out.nodes[a]).toBeUndefined()
    expect(out.nodes[z]).toBeUndefined()
    expect(out.wires[shared]).toBeUndefined()
    expect(out.regions[left]).toBeDefined()
    expect(out.regions[right]).toBeDefined()
  })

  it('deletes selected interior content while dissolving nested boundaries deepest-first', () => {
    const b = new DiagramBuilder()
    const outer = b.cut(b.root)
    const inner = b.cut(outer)
    const doomed = b.ref(inner, 'doomed', 1)
    const kept = b.ref(inner, 'kept', 1)
    const doomedWire = b.wire(inner, [{ node: doomed, port: { kind: 'arg', index: 0 } }])
    const keptWire = b.wire(inner, [{ node: kept, port: { kind: 'arg', index: 0 } }])
    const d = b.build()
    const out = deleteHits(d, [
      { kind: 'region', id: outer },
      { kind: 'region', id: inner },
      { kind: 'node', id: doomed },
    ])
    expect(out.regions[outer]).toBeUndefined()
    expect(out.regions[inner]).toBeUndefined()
    expect(out.nodes[doomed]).toBeUndefined()
    expect(out.wires[doomedWire]).toBeUndefined()
    expect(out.nodes[kept]?.region).toBe(d.root)
    expect(out.wires[keptWire]?.scope).toBe(d.root)
  })
})

describe('node reparenting', () => {
  it('moves private wires, preserves valid shared scopes, and widens invalid shared scopes to the DCA', () => {
    const b = new DiagramBuilder()
    const outer = b.cut(b.root)
    const source = b.cut(outer)
    const target = b.cut(outer)
    const moving = b.termNode(source, p('a b'))
    const peerOuter = b.ref(outer, 'outerPeer', 1)
    const peerSource = b.ref(source, 'sourcePeer', 1)
    const privateWire = b.wire(source, [{ node: moving, port: { kind: 'output' } }])
    const validShared = b.wire(outer, [
      { node: moving, port: { kind: 'freeVar', name: 'a' } },
      { node: peerOuter, port: { kind: 'arg', index: 0 } },
    ])
    const invalidShared = b.wire(source, [
      { node: moving, port: { kind: 'freeVar', name: 'b' } },
      { node: peerSource, port: { kind: 'arg', index: 0 } },
    ])
    const d = b.build()
    const out = reparentNode(d, moving, target)
    expect(out.nodes[moving]?.region).toBe(target)
    expect(out.wires[privateWire]?.scope).toBe(target)
    expect(out.wires[validShared]?.scope).toBe(outer)
    expect(out.wires[invalidShared]?.scope).toBe(outer)
  })

  it('keeps a shared outer scope when moving inward and refuses unknown destinations', () => {
    const b = new DiagramBuilder()
    const cut = b.cut(b.root)
    const moving = b.ref(b.root, 'moving', 1)
    const inside = b.ref(cut, 'inside', 1)
    const shared = b.wire(b.root, [
      { node: moving, port: { kind: 'arg', index: 0 } },
      { node: inside, port: { kind: 'arg', index: 0 } },
    ])
    const d = b.build()
    const out = reparentNode(d, moving, cut)
    expect(out.nodes[moving]?.region).toBe(cut)
    expect(out.wires[shared]?.scope).toBe(d.root)
    expect(() => reparentNode(d, moving, 'ghost')).toThrow(/unknown region 'ghost'/)
    expect(() => reparentNode(d, 'ghost', cut)).toThrow(/unknown node 'ghost'/)
  })
})
