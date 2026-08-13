import {
  mkDiagram,
  portKey,
  type Diagram,
  type DiagramNode,
  type Endpoint,
  type NodeId,
  type Port,
  type Region,
  type RegionId,
  type Wire,
  type WireId,
} from '../kernel/diagram/diagram'
import {
  mkDiagramWithBoundary,
  type DiagramWithBoundary,
} from '../kernel/diagram/boundary'
import { deepestCommonAncestor, isAncestorOrEqual } from '../kernel/diagram/regions'
import {
  relSig,
  sigEquals,
  sigKey,
  type RelSig,
  type Sig,
} from '../kernel/diagram/sig'

export type GraphConstruction = {
  readonly root: RegionId
  readonly regions: Readonly<Record<RegionId, Region>>
  readonly nodes: Readonly<Record<NodeId, DiagramNode>>
  readonly wires: Readonly<Record<WireId, Wire>>
  /**
   * Where each declared wire's quantifier is meant to read. A wire carries no
   * scope of its own; finishing the graph pins the wire at this region so the
   * derived scope is the declared one.
   */
  readonly scopes: Readonly<Record<WireId, RegionId>>
  readonly nextRegion: number
  readonly nextNode: number
  readonly nextWire: number
}

export type GraphResult<T> = {
  readonly graph: GraphConstruction
  readonly value: T
}

export type ImplicationScope = {
  readonly antecedent: RegionId
  readonly consequent: RegionId
}

export type BiconditionalScope = {
  readonly forward: ImplicationScope
  readonly reverse: ImplicationScope
}

export type DisjunctionScope = {
  readonly left: RegionId
  readonly right: RegionId
}

export type QuantifierScope = {
  readonly variables: readonly WireId[]
  readonly body: RegionId
}

function result<T>(graph: GraphConstruction, value: T): GraphResult<T> {
  return Object.freeze({ graph, value })
}

function freezeGraph(graph: GraphConstruction): GraphConstruction {
  return Object.freeze({
    ...graph,
    regions: Object.freeze({ ...graph.regions }),
    nodes: Object.freeze({ ...graph.nodes }),
    wires: Object.freeze({ ...graph.wires }),
    scopes: Object.freeze({ ...graph.scopes }),
  })
}

function requireRegion(graph: GraphConstruction, region: RegionId): void {
  if (graph.regions[region] === undefined) {
    throw new Error(`graph construction: unknown region '${region}'`)
  }
}

function requireWire(graph: GraphConstruction, wire: WireId): Wire {
  const value = graph.wires[wire]
  if (value === undefined) {
    throw new Error(`graph construction: unknown wire '${wire}'`)
  }
  return value
}

function addCut(
  graph: GraphConstruction,
  parent: RegionId,
): GraphResult<RegionId> {
  requireRegion(graph, parent)
  const id = `r${graph.nextRegion}`
  return result(freezeGraph({
    ...graph,
    regions: { ...graph.regions, [id]: { kind: 'cut', parent } },
    nextRegion: graph.nextRegion + 1,
  }), id)
}

function addNode(
  graph: GraphConstruction,
  node: DiagramNode,
): GraphResult<NodeId> {
  requireRegion(graph, node.region)
  const id = `n${graph.nextNode}`
  return result(freezeGraph({
    ...graph,
    nodes: { ...graph.nodes, [id]: node },
    nextNode: graph.nextNode + 1,
  }), id)
}

function attach(
  graph: GraphConstruction,
  wireId: WireId,
  endpoint: Endpoint,
): GraphConstruction {
  const wire = requireWire(graph, wireId)
  if (wire.endpoints.some((candidate) =>
    candidate.node === endpoint.node
    && portKey(candidate.port) === portKey(endpoint.port))) {
    throw new Error(
      `graph construction: endpoint '${endpoint.node}:${portKey(endpoint.port)}' `
      + `is already attached to wire '${wireId}'`,
    )
  }
  return freezeGraph({
    ...graph,
    wires: {
      ...graph.wires,
      [wireId]: {
        ...wire,
        endpoints: Object.freeze([...wire.endpoints, endpoint]),
      },
    },
  })
}

function attachNode(
  graph: GraphConstruction,
  node: NodeId,
  ports: readonly (readonly [WireId, Port])[],
): GraphConstruction {
  let current = graph
  for (const [wire, port] of ports) {
    current = attach(current, wire, { node, port })
  }
  return current
}

function argumentSigs(
  graph: GraphConstruction,
  args: readonly WireId[],
): readonly Sig[] {
  return args.map((wire) => requireWire(graph, wire).sig)
}

function assertApplication(
  graph: GraphConstruction,
  relation: WireId,
  args: readonly WireId[],
): RelSig {
  const relationSig = requireWire(graph, relation).sig
  if (relationSig.kind !== 'rel') {
    throw new Error(
      `graph construction: application head '${relation}' must have a relation signature`,
    )
  }
  const actualArgs = argumentSigs(graph, args)
  if (actualArgs.length !== relationSig.args.length) {
    throw new Error(
      `graph construction: relation '${relation}' expects ${relationSig.args.length} `
      + `arguments, got ${actualArgs.length}`,
    )
  }
  actualArgs.forEach((sig, index) => {
    const expected = relationSig.args[index]!
    if (!sigEquals(sig, expected)) {
      throw new Error(
        `graph construction: relation '${relation}' argument ${index} expects `
        + `'${sigKey(expected)}', got '${sigKey(sig)}'`,
      )
    }
  })
  return relationSig
}

export function emptyGraph(): GraphConstruction {
  return freezeGraph({
    root: 'r0',
    regions: { r0: { kind: 'sheet' } },
    nodes: {},
    wires: {},
    scopes: {},
    nextRegion: 1,
    nextNode: 0,
    nextWire: 0,
  })
}

export function declareWire(
  graph: GraphConstruction,
  scope: RegionId,
  sig: Sig,
): GraphResult<WireId> {
  requireRegion(graph, scope)
  const id = `w${graph.nextWire}`
  return result(freezeGraph({
    ...graph,
    wires: {
      ...graph.wires,
      [id]: { sig, endpoints: Object.freeze([]) },
    },
    scopes: { ...graph.scopes, [id]: scope },
    nextWire: graph.nextWire + 1,
  }), id)
}

export function implication(
  graph: GraphConstruction,
  region: RegionId,
): GraphResult<ImplicationScope> {
  const outer = addCut(graph, region)
  const inner = addCut(outer.graph, outer.value)
  return result(inner.graph, Object.freeze({
    antecedent: outer.value,
    consequent: inner.value,
  }))
}

export function negation(
  graph: GraphConstruction,
  region: RegionId,
): GraphResult<RegionId> {
  return addCut(graph, region)
}

export function disjunction(
  graph: GraphConstruction,
  region: RegionId,
): GraphResult<DisjunctionScope> {
  const outer = addCut(graph, region)
  const left = addCut(outer.graph, outer.value)
  const right = addCut(left.graph, outer.value)
  return result(right.graph, Object.freeze({
    left: left.value,
    right: right.value,
  }))
}

export function biconditional(
  graph: GraphConstruction,
  region: RegionId,
): GraphResult<BiconditionalScope> {
  const forward = implication(graph, region)
  const reverse = implication(forward.graph, region)
  return result(reverse.graph, Object.freeze({
    forward: forward.value,
    reverse: reverse.value,
  }))
}

export function quantifierScope(
  graph: GraphConstruction,
  region: RegionId,
  quantifier: 'exists' | 'forall',
  signatures: readonly Sig[],
): GraphResult<QuantifierScope> {
  requireRegion(graph, region)
  if (signatures.length === 0) {
    return result(graph, Object.freeze({
      variables: Object.freeze([]),
      body: region,
    }))
  }

  let current = graph
  let scope = region
  let body = region
  if (quantifier === 'forall') {
    const outer = addCut(current, region)
    const inner = addCut(outer.graph, outer.value)
    current = inner.graph
    scope = outer.value
    body = inner.value
  }
  const variables: WireId[] = []
  for (const sig of signatures) {
    const variable = declareWire(current, scope, sig)
    current = variable.graph
    variables.push(variable.value)
  }
  return result(current, Object.freeze({
    variables: Object.freeze(variables),
    body,
  }))
}

export function atom(
  graph: GraphConstruction,
  region: RegionId,
  relation: WireId,
  args: readonly WireId[],
): GraphResult<NodeId> {
  const sig = assertApplication(graph, relation, args)
  const created = addNode(graph, { kind: 'atom', region, sig })
  const ports: Array<readonly [WireId, Port]> = [
    [relation, { kind: 'head' }],
    ...args.map((wire, index): readonly [WireId, Port] => [
      wire,
      { kind: 'arg', index },
    ]),
  ]
  return result(attachNode(created.graph, created.value, ports), created.value)
}

export function ref(
  graph: GraphConstruction,
  region: RegionId,
  defId: string,
  args: readonly WireId[],
): GraphResult<NodeId> {
  const sig = relSig(argumentSigs(graph, args))
  const created = addNode(graph, { kind: 'ref', region, defId, sig })
  const ports = args.map((wire, index): readonly [WireId, Port] => [
    wire,
    { kind: 'arg', index },
  ])
  return result(attachNode(created.graph, created.value, ports), created.value)
}

export function identity(
  graph: GraphConstruction,
  region: RegionId,
  wires: readonly WireId[],
): GraphResult<NodeId> {
  if (wires.length < 2) {
    throw new Error('graph construction: identity requires at least two wires')
  }
  const sig = requireWire(graph, wires[0]!).sig
  wires.forEach((wire, index) => {
    const candidate = requireWire(graph, wire).sig
    if (!sigEquals(candidate, sig)) {
      throw new Error(
        `graph construction: identity wire ${index} has signature `
        + `'${sigKey(candidate)}', expected '${sigKey(sig)}'`,
      )
    }
  })
  const created = addNode(graph, {
    kind: 'identity',
    region,
    sig,
    arity: wires.length,
  })
  const ports = wires.map((wire, index): readonly [WireId, Port] => [
    wire,
    { kind: 'identity', index },
  ])
  return result(attachNode(created.graph, created.value, ports), created.value)
}

/**
 * Materialize every declared scope as incidences. A wire's quantifier reads
 * off where its ends are, so a wire whose ends all lie strictly below its
 * declared scope — or which has fewer than the two ends every wire needs —
 * gets unary identity nodes (pins) at the declared region until its derived
 * scope is the declared one and the two-end floor is met. Boundary entries
 * count as ends at the root.
 */
function completed(
  graph: GraphConstruction,
  boundary: readonly WireId[],
): {
  readonly nodes: Record<NodeId, DiagramNode>
  readonly wires: Record<WireId, Wire>
} {
  const nodes: Record<NodeId, DiagramNode> = { ...graph.nodes }
  const wires: Record<WireId, Wire> = { ...graph.wires }
  let nextNode = graph.nextNode

  const boundaryEnds = new Map<WireId, number>()
  for (const wireId of boundary) {
    boundaryEnds.set(wireId, (boundaryEnds.get(wireId) ?? 0) + 1)
  }

  for (const [wireId, wire] of Object.entries(graph.wires)) {
    const declared = graph.scopes[wireId]
    if (declared === undefined) {
      throw new Error(`graph construction: wire '${wireId}' has no declared scope`)
    }
    const boundaryCount = boundaryEnds.get(wireId) ?? 0
    let scope: RegionId | null = boundaryCount > 0 ? graph.root : null
    for (const endpoint of wire.endpoints) {
      const region = nodes[endpoint.node]!.region
      scope = scope === null
        ? region
        : deepestCommonAncestor(graph, scope, region)
    }
    if (scope !== null && !isAncestorOrEqual(graph, declared, scope)) {
      throw new Error(
        `graph construction: wire '${wireId}' is declared at '${declared}', `
        + `which does not enclose its ends at '${scope}'`,
      )
    }
    const endpoints = [...wire.endpoints]
    let ends = endpoints.length + boundaryCount
    while (scope !== declared || ends < 2) {
      const node = `n${nextNode++}`
      nodes[node] = { kind: 'identity', region: declared, sig: wire.sig, arity: 1 }
      endpoints.push({ node, port: { kind: 'identity', index: 0 } })
      scope = declared
      ends += 1
    }
    if (endpoints.length !== wire.endpoints.length) {
      wires[wireId] = { sig: wire.sig, endpoints: Object.freeze(endpoints) }
    }
  }

  return { nodes, wires }
}

export function finishDiagram(graph: GraphConstruction): Diagram {
  const { nodes, wires } = completed(graph, [])
  return mkDiagram({
    root: graph.root,
    regions: { ...graph.regions },
    nodes,
    wires,
  })
}

export function finishDiagramWithBoundary(
  graph: GraphConstruction,
  boundary: readonly WireId[],
): DiagramWithBoundary {
  const { nodes, wires } = completed(graph, boundary)
  return mkDiagramWithBoundary({
    root: graph.root,
    regions: graph.regions,
    nodes,
    wires,
  }, boundary)
}
