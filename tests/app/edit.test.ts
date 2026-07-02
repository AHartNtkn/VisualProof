import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import {
  addTermNode, addCut, addBubble, joinPorts, deleteSelection, emptyDiagram,
} from '../../src/app/edit'

const p = (s: string) => parseTerm(s)

describe('edit operations (construction mode, mkDiagram-validated surgery)', () => {
  it('starts from the empty sheet and adds parsed term nodes with auto wires', () => {
    const d0 = emptyDiagram()
    expect(Object.keys(d0.nodes)).toHaveLength(0)
    const { diagram: d1, node } = addTermNode(d0, d0.root, p('\\x. x y'))
    expect(d1.nodes[node]?.kind).toBe('term')
    // output + y singleton wires materialized
    const touching = Object.values(d1.wires).filter((w) => w.endpoints.some((ep) => ep.node === node))
    expect(touching).toHaveLength(2)
  })

  it('wraps a selection in a single cut and in a bubble', () => {
    const d0 = emptyDiagram()
    const { diagram: d1, node } = addTermNode(d0, d0.root, p('y'))
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
    const a = addTermNode(d0, d0.root, p('\\x. x'))
    const b = addTermNode(a.diagram, a.diagram.root, p('y'))
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
    const a = addTermNode(d0, d0.root, p('\\x. x'))
    const b = addTermNode(a.diagram, a.diagram.root, p('y'))
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
    const a = addTermNode(d0, d0.root, p('\\x. x'))
    const b = addTermNode(a.diagram, a.diagram.root, p('y'))
    expect(() => joinPorts(b.diagram,
      { node: a.node, port: { kind: 'output' } },
      { node: b.node, port: { kind: 'freeVar', name: 'y' } }))
      .toThrowError(/has no port 'v:y' \(its ports are out, v:s0/)
  })

  it('refuses joining a port to itself, loudly', () => {
    const d0 = emptyDiagram()
    const a = addTermNode(d0, d0.root, p('\\x. x'))
    expect(() => joinPorts(a.diagram,
      { node: a.node, port: { kind: 'output' } },
      { node: a.node, port: { kind: 'output' } })).toThrowError(/same port/)
  })
})
