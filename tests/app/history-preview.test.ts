import { describe, expect, it } from 'vitest'
import type { Diagram } from '../../src/kernel/diagram/diagram'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { parseTerm } from '../../src/kernel/term/parse'
import { deriveChangeFocus, previewTransition } from '../../src/app/history-preview'

function fixture() {
  const b = new DiagramBuilder()
  const a = b.termNode(b.root, parseTerm('a'))
  const z = b.termNode(b.root, parseTerm('z'))
  const wire = b.wire(b.root, [
    { node: a, port: { kind: 'freeVar', name: 'a' } },
    { node: z, port: { kind: 'freeVar', name: 'z' } },
  ])
  return { diagram: b.build(), a, z, wire }
}

describe('history preview focus', () => {
  it('focuses added and structurally changed nodes in the after state', () => {
    const one = new DiagramBuilder()
    const a = one.termNode(one.root, parseTerm('a'))
    const before = one.build()
    const two = new DiagramBuilder()
    const sameA = two.termNode(two.root, parseTerm('a'))
    const added = two.termNode(two.root, parseTerm('z'))
    const built = two.build()
    const prior = built.nodes[sameA]!
    if (prior.kind !== 'term') throw new Error('expected term fixture')
    const after: Diagram = {
      ...built,
      nodes: { ...built.nodes, [sameA]: { ...prior, term: parseTerm('\\x. x') } },
    }
    expect(sameA).toBe(a)

    const focus = deriveChangeFocus(before, after)
    expect(focus.kind).toBe('items')
    if (focus.kind === 'items') expect(focus.nodes).toEqual([a, added])
  })

  it('focuses added or structurally changed wires', () => {
    const { diagram, wire } = fixture()
    const without = { ...diagram, wires: {} }
    expect(deriveChangeFocus(without, diagram)).toEqual({ kind: 'items', nodes: [], wires: Object.keys(diagram.wires).sort() })

    const changed: Diagram = {
      ...diagram,
      wires: { ...diagram.wires, [wire]: { ...diagram.wires[wire]!, endpoints: diagram.wires[wire]!.endpoints.slice(0, 1) } },
    }
    expect(deriveChangeFocus(diagram, changed)).toEqual({ kind: 'items', nodes: [], wires: [wire] })
  })

  it('uses surviving incident nodes to show wire and node removals', () => {
    const { diagram, a, z, wire } = fixture()
    const noWire: Diagram = { ...diagram, wires: {} }
    expect(deriveChangeFocus(diagram, noWire)).toEqual({ kind: 'items', nodes: [a, z], wires: [] })

    const noZ: Diagram = {
      ...diagram,
      nodes: { [a]: diagram.nodes[a]! },
      wires: {},
    }
    expect(deriveChangeFocus(diagram, noZ)).toEqual({ kind: 'items', nodes: [a], wires: [] })
    expect(diagram.nodes[z]).toBeDefined()
    expect(diagram.wires[wire]).toBeDefined()
  })

  it('falls back to the whole diagram and resolves edge transitions', () => {
    const { diagram } = fixture()
    expect(deriveChangeFocus(diagram, diagram)).toEqual({ kind: 'diagram' })
    expect(previewTransition([diagram], 0)).toEqual({ before: diagram, after: diagram, focus: { kind: 'diagram' } })
  })
})
