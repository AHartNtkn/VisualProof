import type {
  Diagram,
  NodeId,
  RegionId,
  WireId,
} from '../kernel/diagram/diagram'
import type { DiagramWithBoundary } from '../kernel/diagram/boundary'
import {
  IOTA,
  relSig,
  sigEquals,
  type RelSig,
  type Sig,
} from '../kernel/diagram/sig'
import { findDeiterationEvidence } from '../kernel/rules/iteration'
import type { SubgraphSelection } from '../kernel/diagram/subgraph/selection'
import {
  atom,
  declareWire,
  emptyGraph,
  finishDiagramWithBoundary,
  implication,
  quantifierScope,
  type GraphConstruction,
} from './graph'

export const UNARY = relSig([IOTA])
export const BINARY = relSig([IOTA, IOTA])
export const TERNARY = relSig([IOTA, IOTA, IOTA])

export function relationApplicationContent(
  signature: RelSig,
): DiagramWithBoundary {
  let graph = emptyGraph()
  const formals: WireId[] = []
  for (const argumentSignature of signature.args) {
    const argument = declareWire(
      graph,
      graph.root,
      argumentSignature,
    )
    graph = argument.graph
    formals.push(argument.value)
  }
  const relation = declareWire(graph, graph.root, signature)
  graph = relation.graph
  graph = atom(graph, graph.root, relation.value, formals).graph
  return finishDiagramWithBoundary(
    graph,
    [...formals, relation.value],
  )
}

type UnaryCarrierDrawer = (
  graph: GraphConstruction,
  region: RegionId,
  formal: WireId,
  captures: readonly WireId[],
) => GraphConstruction

function unaryCarrierContent(
  captureSignatures: readonly Sig[],
  draw: UnaryCarrierDrawer,
): DiagramWithBoundary {
  let graph = emptyGraph()
  const formal = declareWire(graph, graph.root, IOTA)
  graph = formal.graph
  const captures: WireId[] = []
  for (const signature of captureSignatures) {
    const capture = declareWire(graph, graph.root, signature)
    graph = capture.graph
    captures.push(capture.value)
  }
  graph = draw(graph, graph.root, formal.value, captures)
  return finishDiagramWithBoundary(
    graph,
    [formal.value, ...captures],
  )
}

function additionTotality(
  initial: GraphConstruction,
  region: RegionId,
  formal: WireId,
  plus: WireId,
): GraphConstruction {
  const quantified = quantifierScope(initial, region, 'forall', [IOTA])
  const right = quantified.value.variables[0]!
  const output = declareWire(
    quantified.graph,
    quantified.value.body,
    IOTA,
  )
  return atom(
    output.graph,
    quantified.value.body,
    plus,
    [formal, right, output.value],
  ).graph
}

export function rightIdentityCarrierContent(): DiagramWithBoundary {
  return unaryCarrierContent([UNARY, TERNARY], (
    initial,
    region,
    formal,
    [zero, plus],
  ) => {
    const quantified = quantifierScope(initial, region, 'forall', [IOTA])
    const zeroValue = quantified.value.variables[0]!
    const claim = implication(quantified.graph, quantified.value.body)
    let graph = claim.graph
    graph = atom(graph, claim.value.antecedent, zero!, [zeroValue]).graph
    return atom(
      graph,
      claim.value.consequent,
      plus!,
      [formal, zeroValue, formal],
    ).graph
  })
}

export function associativityCarrierContent(): DiagramWithBoundary {
  return unaryCarrierContent([TERNARY], (
    initial,
    region,
    formal,
    [plus],
  ) => {
    let graph = additionTotality(initial, region, formal, plus!)
    const quantified = quantifierScope(
      graph,
      region,
      'forall',
      [IOTA, IOTA, IOTA, IOTA],
    )
    const [right, third, firstSum, innerSum] =
      quantified.value.variables
    const claim = implication(quantified.graph, quantified.value.body)
    graph = claim.graph
    graph = atom(
      graph,
      claim.value.antecedent,
      plus!,
      [formal, right!, firstSum!],
    ).graph
    graph = atom(
      graph,
      claim.value.antecedent,
      plus!,
      [right!, third!, innerSum!],
    ).graph
    const output = declareWire(graph, claim.value.consequent, IOTA)
    graph = output.graph
    graph = atom(
      graph,
      claim.value.consequent,
      plus!,
      [firstSum!, third!, output.value],
    ).graph
    return atom(
      graph,
      claim.value.consequent,
      plus!,
      [formal, innerSum!, output.value],
    ).graph
  })
}

export function successorShiftCarrierContent(): DiagramWithBoundary {
  return unaryCarrierContent([BINARY, TERNARY], (
    initial,
    region,
    formal,
    [successor, plus],
  ) => {
    const withTotality = additionTotality(
      initial,
      region,
      formal,
      plus!,
    )
    const quantified = quantifierScope(
      withTotality,
      region,
      'forall',
      [IOTA, IOTA, IOTA, IOTA],
    )
    const [right, rightSuccessor, output, outputSuccessor] =
      quantified.value.variables
    const claim = implication(quantified.graph, quantified.value.body)
    let graph = claim.graph
    graph = atom(
      graph,
      claim.value.antecedent,
      successor!,
      [right!, rightSuccessor!],
    ).graph
    graph = atom(
      graph,
      claim.value.antecedent,
      plus!,
      [formal, right!, output!],
    ).graph
    graph = atom(
      graph,
      claim.value.antecedent,
      successor!,
      [output!, outputSuccessor!],
    ).graph
    return atom(
      graph,
      claim.value.consequent,
      plus!,
      [formal, rightSuccessor!, outputSuccessor!],
    ).graph
  })
}

export function commutativityCarrierContent(): DiagramWithBoundary {
  return unaryCarrierContent([TERNARY, IOTA], (
    initial,
    region,
    formal,
    [plus, fixedRight],
  ) => {
    const withTotality = additionTotality(
      initial,
      region,
      formal,
      plus!,
    )
    const quantified = quantifierScope(
      withTotality,
      region,
      'forall',
      [IOTA],
    )
    const output = quantified.value.variables[0]!
    const claim = implication(quantified.graph, quantified.value.body)
    let graph = claim.graph
    graph = atom(
      graph,
      claim.value.antecedent,
      plus!,
      [formal, fixedRight!, output],
    ).graph
    return atom(
      graph,
      claim.value.consequent,
      plus!,
      [fixedRight!, formal, output],
    ).graph
  })
}

export function directCuts(
  diagram: Diagram,
  parent: RegionId,
): readonly RegionId[] {
  return Object.entries(diagram.regions)
    .filter(([, region]) =>
      region.kind === 'cut' && region.parent === parent)
    .map(([id]) => id)
}

export function directNodes(
  diagram: Diagram,
  region: RegionId,
): readonly NodeId[] {
  return Object.entries(diagram.nodes)
    .filter(([, node]) => node.region === region)
    .map(([id]) => id)
}

export function scopedWires(
  diagram: Diagram,
  region: RegionId,
): readonly WireId[] {
  return Object.entries(diagram.wires)
    .filter(([, wire]) => wire.scope === region)
    .map(([id]) => id)
}

export function introducedContentSelection(
  before: Diagram,
  after: Diagram,
  region: RegionId,
): SubgraphSelection {
  return {
    region,
    regions: directCuts(after, region)
      .filter((id) => before.regions[id] === undefined),
    nodes: directNodes(after, region)
      .filter((id) => before.nodes[id] === undefined),
    wires: scopedWires(after, region)
      .filter((id) => before.wires[id] === undefined),
  }
}

export function exactOne<T>(
  values: readonly T[],
  what: string,
): T {
  if (values.length !== 1) {
    throw new Error(`expected exactly one ${what}, found ${values.length}`)
  }
  return values[0]!
}

export type NatHereditaryParts = {
  readonly inherited: RegionId
  readonly baseCondition: RegionId
  readonly closureCondition: RegionId
}

export function natHereditaryParts(
  diagram: Diagram,
  hereditary: RegionId,
): NatHereditaryParts {
  const children = directCuts(diagram, hereditary)
  return {
    inherited: exactOne(
      children.filter((region) =>
        scopedWires(diagram, region).length === 0),
      'inherited result',
    ),
    baseCondition: exactOne(
      children.filter((region) =>
        scopedWires(diagram, region).length === 1),
      'Nat base condition',
    ),
    closureCondition: exactOne(
      children.filter((region) =>
        scopedWires(diagram, region).length === 2),
      'Nat closure condition',
    ),
  }
}

export function endpointWire(
  diagram: Diagram,
  nodeId: NodeId,
  kind: 'head' | 'arg' | 'identity',
  index?: number,
): WireId {
  return exactOne(
    Object.entries(diagram.wires)
      .filter(([, wire]) => wire.endpoints.some((endpoint) =>
        endpoint.node === nodeId
        && endpoint.port.kind === kind
        && (
          kind === 'head'
          || (
            endpoint.port.kind !== 'head'
            && endpoint.port.index === index
          )
        )))
      .map(([id]) => id),
    `${kind}${index === undefined ? '' : ` ${index}`} wire on '${nodeId}'`,
  )
}

export function nodeWithHead(
  diagram: Diagram,
  region: RegionId,
  relation: WireId,
): NodeId {
  return exactOne(
    directNodes(diagram, region).filter((node) =>
      diagram.nodes[node]!.kind === 'atom'
      && endpointWire(diagram, node, 'head') === relation),
    `atom headed by '${relation}' in '${region}'`,
  )
}

export function relationWire(
  diagram: Diagram,
  scope: RegionId,
  signature: typeof UNARY,
): WireId {
  return exactOne(
    scopedWires(diagram, scope).filter((wire) =>
      sigEquals(diagram.wires[wire]!.sig, signature)),
    `relation wire in '${scope}'`,
  )
}

export function deiterationStep(
  diagram: Diagram,
  region: RegionId,
  node: NodeId,
) {
  const sel = {
    region,
    regions: [],
    nodes: [node],
    wires: [],
  } as const
  const evidence = findDeiterationEvidence(diagram, sel, 4096)
  return {
    rule: 'deiteration',
    sel,
    justifier: evidence.justifier,
    certificate: evidence.certificate,
    retargets: [],
  } as const
}

export function deiterationSelectionStep(
  diagram: Diagram,
  sel: SubgraphSelection,
) {
  const evidence = findDeiterationEvidence(diagram, sel, 4096)
  return {
    rule: 'deiteration',
    sel,
    justifier: evidence.justifier,
    certificate: evidence.certificate,
    retargets: [],
  } as const
}
