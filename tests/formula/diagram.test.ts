import { describe, expect, it } from 'vitest'

import { exploreForm, IOTA, relSig } from '../../src/kernel/diagram'
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
})
