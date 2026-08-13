import { describe, expect, it } from 'vitest'

import { exploreForm, IOTA, relSig } from '../../src/kernel/diagram'
import { derivedScope } from '../../src/kernel/diagram/regions'
import { identityGeometry } from '../../src/view/bend'
import { mkEngine, pkey, worldBindAnchor } from '../../src/view/engine'
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

    expect(derivedScope(diagram, 'w2')).toBe('r5')
    expect(diagram.regions.r5).toEqual({ kind: 'cut', parent: 'r4' })

    for (const wireId of ['w0', 'w1', 'w3', 'w4', 'w5', 'w6', 'w7']) {
      const scope = derivedScope(diagram, wireId)
      expect(diagram.regions[scope]!.kind).toBe('cut')
      expect(Object.values(diagram.regions).filter((region) =>
        region.kind === 'cut' && region.parent === scope,
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

  it('draws individual equality as one dangling-existential-style identity node', () => {
    const diagram = formulaToDiagram('∀ x y. x = y')
    const entry = Object.entries(diagram.nodes).find(([, node]) => node.kind === 'identity')

    expect(entry?.[1]).toEqual({
      kind: 'identity',
      region: 'r2',
      sig: IOTA,
      arity: 2,
    })
    const engine = mkEngine(diagram, [])
    const body = engine.bodies.get(entry![0])
    expect(body?.kind).toBe('identity')
    expect(body?.geometry).toEqual(identityGeometry(2))
    const incidences = Object.entries(diagram.wires).flatMap(([wire, value]) =>
      value.endpoints
        .filter((endpoint) => endpoint.node === entry![0])
        .map((endpoint) => ({ wire, port: endpoint.port })))
    expect(incidences.map(({ port }) => port)).toEqual([
      { kind: 'identity', index: 0 },
      { kind: 'identity', index: 1 },
    ])
    expect(new Set(incidences.map(({ wire }) => wire)).size).toBe(2)
    const identityBinds = incidences.map(({ wire, port }) =>
      engine.wires.get(wire)!.binds.find((bind) => bind.body === entry![0] && bind.key === pkey(port))!)
    expect(new Set(identityBinds.map((bind) => bind.key)).size).toBe(identityBinds.length)
    body!.pos = { x: 13, y: -7 }
    body!.theta = Math.PI / 4
    engine.scale = 1.5
    for (const bind of identityBinds) {
      const local = body!.localAnchor.get(bind.key)!
      const c = Math.cos(body!.theta), s = Math.sin(body!.theta)
      const world = worldBindAnchor(engine, body!, bind.key)
      expect(Math.hypot(local.x, local.y)).toBeGreaterThan(0)
      expect(world.x).toBeCloseTo(body!.pos.x + engine.scale * (local.x * c - local.y * s), 9)
      expect(world.y).toBeCloseTo(body!.pos.y + engine.scale * (local.x * s + local.y * c), 9)
    }
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

  it('draws an equality chain as one multi-port dangling-existential-style identity node', () => {
    const diagram = formulaToDiagram('∀ x y z. x = y = z')
    // the three binder pins are arity-1 identities too; the chain itself is the
    // single multi-port one
    const pins = Object.entries(diagram.nodes)
      .filter(([, node]) => node.kind === 'identity' && node.arity === 1)
    const entries = Object.entries(diagram.nodes)
      .filter(([, node]) => node.kind === 'identity' && node.arity !== 1)

    expect(pins.map(([, node]) => node.kind === 'identity' && node.region)).toEqual(['r1', 'r1', 'r1'])
    expect(entries).toHaveLength(1)
    expect(entries[0]![1]).toEqual({
      kind: 'identity',
      region: 'r2',
      sig: IOTA,
      arity: 3,
    })
    const engine = mkEngine(diagram, [])
    const body = engine.bodies.get(entries[0]![0])
    expect(body?.kind).toBe('identity')
    expect(body?.geometry).toEqual(identityGeometry(3))
    const incidences = Object.entries(diagram.wires).flatMap(([wire, value]) =>
      value.endpoints
        .filter((endpoint) => endpoint.node === entries[0]![0])
        .map((endpoint) => ({ wire, port: endpoint.port })))
    expect(incidences.map(({ port }) => port)).toEqual([
      { kind: 'identity', index: 0 },
      { kind: 'identity', index: 1 },
      { kind: 'identity', index: 2 },
    ])
    expect(new Set(incidences.map(({ wire }) => wire)).size).toBe(3)
    const identityBinds = incidences.map(({ wire, port }) =>
      engine.wires.get(wire)!.binds.find((bind) => bind.body === entries[0]![0] && bind.key === pkey(port))!)
    expect(new Set(identityBinds.map((bind) => bind.key)).size).toBe(identityBinds.length)
    body!.pos = { x: -9, y: 5 }
    body!.theta = -Math.PI / 6
    engine.scale = 2
    for (const bind of identityBinds) {
      const local = body!.localAnchor.get(bind.key)!
      const c = Math.cos(body!.theta), s = Math.sin(body!.theta)
      const world = worldBindAnchor(engine, body!, bind.key)
      expect(Math.hypot(local.x, local.y)).toBeGreaterThan(0)
      expect(world.x).toBeCloseTo(body!.pos.x + engine.scale * (local.x * c - local.y * s), 9)
      expect(world.y).toBeCloseTo(body!.pos.y + engine.scale * (local.x * s + local.y * c), 9)
    }
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
    // one atom per branch, plus the r1 pin each head wire's quantifier sits on
    expect(Object.values(diagram.nodes).map((node) => node.region)).toEqual(['r4', 'r5', 'r1', 'r1'])
  })

  it('draws biconditional as both directed implications', () => {
    const diagram = formulaToDiagram('∀ A B : o. A ↔ B')

    expect(Object.values(diagram.regions).filter((region) => region.kind === 'cut')).toHaveLength(6)
    expect(Object.values(diagram.nodes).filter((node) => node.kind === 'atom')).toHaveLength(4)
  })
})
