import { describe, expect, it } from 'vitest'

import { exploreForm, IOTA, relSig } from '../../src/kernel/diagram'
import { identityGeometry } from '../../src/view/bend'
import { mkEngine } from '../../src/view/engine'
import {
  atom,
  emptyGraph,
  finishDiagram,
  implication,
  quantifierScope,
} from '../../src/theories/graph'
import { formulaToDiagram } from '../../src/formula'

const EXAMPLE_SOURCE = '∀ Z : i → o. ∀ S : i → i → o. (∃ z. Z(z)) ⇒ (∀ z. Z(z) ⇒ (∀ P : i → o. ((∀ n. Z(n) ⇒ P(n)) & (∀ n m. (P(n) & S(n, m)) ⇒ P(m))) ⇒ P(z)))'

function manuallyBuiltUniversalImplication() {
  let graph = emptyGraph()
  const predicates = quantifierScope(graph, graph.root, 'forall', [relSig([IOTA])])
  graph = predicates.graph
  const predicate = predicates.value.variables[0]!
  const individuals = quantifierScope(graph, predicates.value.body, 'forall', [IOTA])
  graph = individuals.graph
  const individual = individuals.value.variables[0]!
  const scope = implication(graph, individuals.value.body)
  graph = scope.graph
  graph = atom(graph, scope.value.antecedent, predicate, [individual]).graph
  graph = atom(graph, scope.value.consequent, predicate, [individual]).graph
  return finishDiagram(graph)
}

describe('formulaToDiagram', () => {
  it('draws the typed example with its scopes, heads, and argument signatures intact', () => {
    const diagram = formulaToDiagram(EXAMPLE_SOURCE)

    expect(Object.values(diagram.regions).filter((region) => region.kind === 'cut')).toHaveLength(22)
    expect(Object.values(diagram.nodes).filter((node) => node.kind === 'atom')).toHaveLength(8)
    expect(Object.values(diagram.wires)).toHaveLength(8)

    expect(diagram.wires.w0!.endpoints.filter((endpoint) => endpoint.port.kind === 'head')).toHaveLength(3)
    expect(diagram.wires.w1!.endpoints.filter((endpoint) => endpoint.port.kind === 'head')).toHaveLength(1)
    expect(diagram.wires.w4!.endpoints.filter((endpoint) => endpoint.port.kind === 'head')).toHaveLength(4)

    expect(diagram.wires.w2!.scope).toBe('r5')
    expect(diagram.regions.r5).toEqual({ kind: 'cut', parent: 'r4' })

    for (const wire of [
      diagram.wires.w0!,
      diagram.wires.w1!,
      diagram.wires.w3!,
      diagram.wires.w4!,
      diagram.wires.w5!,
      diagram.wires.w6!,
      diagram.wires.w7!,
    ]) {
      expect(diagram.regions[wire.scope]!.kind).toBe('cut')
      expect(Object.values(diagram.regions).filter((region) =>
        region.kind === 'cut' && region.parent === wire.scope,
      )).toHaveLength(1)
    }

    for (const wire of Object.values(diagram.wires)) {
      for (const endpoint of wire.endpoints) {
        if (endpoint.port.kind === 'arg') expect(wire.sig).toEqual(IOTA)
      }
    }
  })

  it('is structurally equivalent to an independently constructed universal implication', () => {
    expect(exploreForm(formulaToDiagram('∀ P : i → o. ∀ x. P(x) ⇒ P(x)')))
      .toBe(exploreForm(manuallyBuiltUniversalImplication()))
  })

  it('restores an outer binding after a shadowing quantifier', () => {
    const diagram = formulaToDiagram('∀ P : i → o. ∀ x. (∃ x. P(x)) & P(x)')

    expect(diagram.wires.w1!.endpoints.filter((endpoint) => endpoint.port.kind === 'arg')).toHaveLength(1)
    expect(diagram.wires.w2!.endpoints.filter((endpoint) => endpoint.port.kind === 'arg')).toHaveLength(1)
  })

  it('draws individual equality as a compact identity node', () => {
    const diagram = formulaToDiagram('∀ x y. x = y')
    const entry = Object.entries(diagram.nodes).find(([, node]) => node.kind === 'identity')

    expect(entry?.[1]).toEqual({
      kind: 'identity',
      region: 'r2',
      sig: IOTA,
      arity: 2,
    })
    const body = mkEngine(diagram, []).bodies.get(entry![0])
    expect(body?.kind).toBe('identity')
    expect(body?.geometry).toEqual(identityGeometry(2))
  })

  it('draws equality between relation variables with their shared signature', () => {
    const signature = relSig([IOTA])
    const diagram = formulaToDiagram('∀ P Q : i → o. P = Q')
    const node = Object.values(diagram.nodes).find((candidate) => candidate.kind === 'identity')

    expect(node).toEqual({
      kind: 'identity',
      region: 'r2',
      sig: signature,
      arity: 2,
    })
  })

  it('draws an equality chain as one compact multi-port identity node', () => {
    const diagram = formulaToDiagram('∀ x y z. x = y = z')
    const entries = Object.entries(diagram.nodes)
      .filter(([, node]) => node.kind === 'identity')

    expect(entries).toHaveLength(1)
    expect(entries[0]![1]).toEqual({
      kind: 'identity',
      region: 'r2',
      sig: IOTA,
      arity: 3,
    })
    const body = mkEngine(diagram, []).bodies.get(entries[0]![0])
    expect(body?.kind).toBe('identity')
    expect(body?.geometry).toEqual(identityGeometry(3))
  })

  it('draws negation as one cut around its body', () => {
    const diagram = formulaToDiagram('∀ A : o. ¬A')

    expect(diagram.regions.r3).toEqual({ kind: 'cut', parent: 'r2' })
    expect(diagram.nodes.n0).toMatchObject({ kind: 'atom', region: 'r3' })
  })

  it('draws disjunction as a cut containing one negated branch per operand', () => {
    const diagram = formulaToDiagram('∀ A B : o. A ∨ B')

    expect(diagram.regions.r3).toEqual({ kind: 'cut', parent: 'r2' })
    expect(diagram.regions.r4).toEqual({ kind: 'cut', parent: 'r3' })
    expect(diagram.regions.r5).toEqual({ kind: 'cut', parent: 'r3' })
    expect(Object.values(diagram.nodes).map((node) => node.region)).toEqual(['r4', 'r5'])
  })

  it('draws biconditional as both directed implications', () => {
    const diagram = formulaToDiagram('∀ A B : o. A ↔ B')

    expect(Object.values(diagram.regions).filter((region) => region.kind === 'cut')).toHaveLength(6)
    expect(Object.values(diagram.nodes).filter((node) => node.kind === 'atom')).toHaveLength(4)
  })
})
