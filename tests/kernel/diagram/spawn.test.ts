import { describe, it, expect } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { portKey } from '../../../src/kernel/diagram/diagram'
import { spawnBoundRelationNode, spawnRelationNode, spawnTermNode } from '../../../src/kernel/diagram/spawn'
import { TERM, relSig, sigKey } from '../../../src/kernel/diagram/sig'
import { parseTerm } from '../../../src/kernel/term/parse'
import type { IdReservation } from '../../../src/kernel/diagram/subgraph/freshId'

const p = (s: string) => parseTerm(s)

describe('spawnTermNode', () => {
  it('adds a term node with a fresh id and TERM-sig wires for output plus each declared free port', () => {
    const d = new DiagramBuilder().build()
    const { diagram, node } = spawnTermNode(d, d.root, p('\\x. y x'))
    expect(node).toBe('n') // freshId's own counter, independent of the builder's n0, n1, … scheme

    expect(diagram.nodes[node]).toMatchObject({ kind: 'term', region: d.root })
    const wires = Object.values(diagram.wires)
    expect(wires).toHaveLength(2) // out, v:y (x is bound, not free)
    for (const w of wires) {
      expect(sigKey(w.sig)).toBe(sigKey(TERM))
      expect(w.scope).toBe(d.root)
    }
  })

  it('picks a fresh node id avoiding both taken and reserved ids', () => {
    const d = new DiagramBuilder().build() // empty, so freshId's first candidate 'n' is otherwise free
    const reservation: IdReservation = { regions: new Set(), nodes: new Set(['n']), wires: new Set() }
    const { node } = spawnTermNode(d, d.root, p('y'), ['y'], reservation)
    expect(node).toBe('n_0')
  })
})

describe('spawnRelationNode', () => {
  it('adds a ref node with arg ports 0..arity-1 sig-typed from the given sig (no head, no output)', () => {
    const d = new DiagramBuilder().build()
    const sig = relSig([TERM, relSig([TERM])])
    const { diagram, node } = spawnRelationNode(d, d.root, 'Nat', sig)
    expect(diagram.nodes[node]).toMatchObject({ kind: 'ref', defId: 'Nat', sig })
    const wires = Object.values(diagram.wires)
    expect(wires).toHaveLength(2)
    const byPort = new Map(wires.flatMap((w) => w.endpoints.map((ep) => [portKey(ep.port), w] as const)))
    expect(sigKey(byPort.get('a:0')!.sig)).toBe(sigKey(TERM))
    expect(sigKey(byPort.get('a:1')!.sig)).toBe(sigKey(relSig([TERM])))
  })

  it('arity-0 ref spawns with no arg wires at all', () => {
    const d = new DiagramBuilder().build()
    const { diagram, node } = spawnRelationNode(d, d.root, 'Zero', relSig([]))
    expect(Object.values(diagram.wires)).toHaveLength(0)
    expect(diagram.nodes[node]).toMatchObject({ kind: 'ref', defId: 'Zero', sig: relSig([]) })
  })
})

describe('spawnBoundRelationNode', () => {
  it('binds a fresh atom to the designated relational wire: head joins it, fresh arg wires are sig-typed from sig.args', () => {
    const b = new DiagramBuilder()
    const target = b.relWire(b.root, relSig([TERM, relSig([TERM])]))
    const d = b.build()
    expect(d.wires[target]!.endpoints).toEqual([])

    const { diagram, node } = spawnBoundRelationNode(d, b.root, target)

    expect(diagram.nodes[node]).toMatchObject({ kind: 'atom', region: b.root, sig: relSig([TERM, relSig([TERM])]) })
    expect(diagram.wires[target]!.endpoints).toEqual([{ node, port: { kind: 'head' } }])
    expect(diagram.wires[target]!.sig).toEqual(relSig([TERM, relSig([TERM])]))

    const argWires = Object.entries(diagram.wires).filter(([id]) => id !== target)
    expect(argWires).toHaveLength(2)
    const byPort = new Map(argWires.flatMap(([, w]) => w.endpoints.map((ep) => [portKey(ep.port), w] as const)))
    expect(sigKey(byPort.get('a:0')!.sig)).toBe(sigKey(TERM))
    expect(sigKey(byPort.get('a:1')!.sig)).toBe(sigKey(relSig([TERM])))
    for (const [, w] of argWires) expect(w.scope).toBe(b.root)
  })

  it('joins an existing endpoint set — a wire already carrying one atom head can bind a second', () => {
    const b = new DiagramBuilder()
    const sig = relSig([TERM])
    const first = b.atom(b.root, sig)
    const target = b.wire(b.root, [{ node: first, port: { kind: 'head' } }], sig)
    const d = b.build()

    const { diagram, node } = spawnBoundRelationNode(d, b.root, target)

    expect(diagram.wires[target]!.endpoints).toEqual([
      { node: first, port: { kind: 'head' } },
      { node, port: { kind: 'head' } },
    ])
  })

  it('spawns arity-0 with no arg wires and only the head endpoint added', () => {
    const b = new DiagramBuilder()
    const target = b.relWire(b.root, relSig([]))
    const d = b.build()

    const { diagram, node } = spawnBoundRelationNode(d, b.root, target)

    expect(Object.keys(diagram.wires)).toEqual([target])
    expect(diagram.wires[target]!.endpoints).toEqual([{ node, port: { kind: 'head' } }])
  })

  it('accepts placing the atom exactly at the wire scope', () => {
    const b = new DiagramBuilder()
    const cut = b.cut(b.root)
    const target = b.relWire(cut, relSig([]))
    const d = b.build()

    const { node } = spawnBoundRelationNode(d, cut, target)
    expect(node).toBe('n')
  })

  it('rejects placing the atom in a region the wire scope does not enclose (scope is a descendant of the region)', () => {
    const b = new DiagramBuilder()
    const cut = b.cut(b.root)
    const target = b.relWire(cut, relSig([]))
    const d = b.build()

    expect(() => spawnBoundRelationNode(d, b.root, target))
      .toThrowError(/does not enclose node/)
  })

  it('throws DiagramError naming the wire when the wire id does not exist', () => {
    const d = new DiagramBuilder().build()
    expect(() => spawnBoundRelationNode(d, d.root, 'ghost'))
      .toThrowError(/spawnBoundRelationNode: wire 'ghost' does not exist/)
  })

  it('throws DiagramError when the designated wire carries a TERM sig, not a relation', () => {
    const b = new DiagramBuilder()
    const term = b.termNode(b.root, p('x'))
    const output = b.wire(b.root, [{ node: term, port: { kind: 'output' } }])
    const d = b.build()
    expect(() => spawnBoundRelationNode(d, b.root, output))
      .toThrowError(/spawnBoundRelationNode: wire '.*' has sig 'term', expected a relation signature/)
  })

  it('picks a fresh node id avoiding both taken and reserved ids', () => {
    const b = new DiagramBuilder()
    const target = b.relWire(b.root, relSig([]))
    const d = b.build() // no nodes yet, so freshId's first candidate 'n' is otherwise free
    const reservation: IdReservation = { regions: new Set(), nodes: new Set(['n']), wires: new Set() }
    const { node } = spawnBoundRelationNode(d, b.root, target, reservation)
    expect(node).toBe('n_0')
  })
})
