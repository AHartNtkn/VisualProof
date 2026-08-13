import type {
  Diagram,
  DiagramNode,
  Endpoint,
  NodeId,
  Region,
  RegionId,
  Wire,
  WireId,
} from '../diagram/diagram'
import {
  DiagramError,
  mkDiagram,
} from '../diagram/diagram'
import type { DiagramWithBoundary } from '../diagram/boundary'
import { derivedScope } from '../diagram/regions'
import { completeWireEnds } from './wire-ends'
import { exploreForm } from '../diagram/canonical/explore'
import type { RelSig } from '../diagram/sig'
import { relSig, sigEquals, sigKey } from '../diagram/sig'
import { extractSubgraph } from '../diagram/subgraph/extract'
import { freshId, type IdReservation } from '../diagram/subgraph/freshId'
import { mkSelection, type SubgraphSelection } from '../diagram/subgraph/selection'
import { removeSubgraph, removeSubgraphParts, spliceSubgraphMapped } from '../diagram/subgraph/splice'
import { refNodeAt, wireAt } from './access'
import { RuleError } from './error'

/** The exact recursive signature exposed by a stored definition's ordered boundary. */
export function definitionSig(definition: DiagramWithBoundary): RelSig {
  return relSig(definition.boundary.map((wire) => definition.diagram.wires[wire]!.sig))
}

function definitionAt(
  definitions: ReadonlyMap<string, DiagramWithBoundary>,
  defId: string,
  operation: 'fold' | 'unfold',
): DiagramWithBoundary {
  const definition = definitions.get(defId)
  if (definition === undefined) throw new RuleError(`${operation}: no relation named '${defId}'`)
  return definition
}

function assertDefinitionSig(
  operation: 'fold' | 'unfold',
  defId: string,
  actual: RelSig,
  expected: RelSig,
): void {
  if (!sigEquals(actual, expected)) {
    throw new RuleError(
      `${operation}: reference signature '${sigKey(actual)}' `
      + `does not match definition '${defId}' signature '${sigKey(expected)}'`,
    )
  }
}

/**
 * Replace one reference with a fresh copy of its stored definition. The
 * definition store is the only transparency authority: atoms are never
 * unfolded. Ordered definition-boundary incidences land on the reference's
 * ordered argument wires; splice owns freshening and identity normalization.
 */
export function applyUnfold(
  diagram: Diagram,
  refNode: NodeId,
  definitions: ReadonlyMap<string, DiagramWithBoundary>,
  reservation?: IdReservation,
): Diagram {
  const ref = refNodeAt(diagram, refNode)
  const definition = definitionAt(definitions, ref.defId, 'unfold')
  assertDefinitionSig('unfold', ref.defId, ref.sig, definitionSig(definition))
  const attachments = ref.sig.args.map((_, index) =>
    wireAt(diagram, refNode, { kind: 'arg', index }))
  const spliced = spliceSubgraphMapped(
    diagram,
    ref.region,
    definition,
    attachments,
    { reserved: reservation },
  ).diagram
  return removeSubgraph(spliced, {
    region: ref.region,
    regions: [],
    nodes: [refNode],
    wires: [],
  })
}

/**
 * Materialize the definition in a host shell carrying the candidate argument
 * scopes, then extract the exact content that unfold would have produced.
 * This deliberately delegates repeated-boundary equality to splice: distinct
 * outer attachments create a local identity, while identical/co-scoped
 * attachments may normalize to a shared wire.
 */
function expectedFoldOccurrence(
  host: Diagram,
  region: RegionId,
  args: readonly WireId[],
  definition: DiagramWithBoundary,
): ReturnType<typeof extractSubgraph> {
  // The comparison shell reproduces each argument wire at its host derived
  // scope as a bare two-pin segment (the drawable stand-in for the old
  // scope-carrying empty wire). The pins are shell scaffolding and are
  // excluded from the expected-occurrence selection below.
  const shellWires: Record<WireId, Wire> = {}
  const shellNodes: Record<string, DiagramNode> = {}
  const shellPinIds = new Set<string>()
  let pinCount = 0
  for (const wireId of new Set(args)) {
    const wire = host.wires[wireId]!
    const scope = derivedScope(host, wireId)
    const endpoints: Endpoint[] = []
    for (let i = 0; i < 2; i += 1) {
      const pin = `shellpin${pinCount++}`
      shellPinIds.add(pin)
      shellNodes[pin] = { kind: 'identity', region: scope, sig: wire.sig, arity: 1 }
      endpoints.push({ node: pin, port: { kind: 'identity', index: 0 } })
    }
    shellWires[wireId] = { sig: wire.sig, endpoints }
  }
  const shell = mkDiagram({
    root: host.root,
    regions: { ...host.regions },
    nodes: shellNodes,
    wires: shellWires,
  })
  const mapped = spliceSubgraphMapped(shell, region, definition, args)
  const definitionRoot = definition.diagram.root
  const regions = Object.entries(definition.diagram.regions)
    .filter(([, candidate]) =>
      candidate.kind === 'cut' && candidate.parent === definitionRoot)
    .map(([regionId]) => mapped.regionMap.get(regionId)!)
  const nodes = Object.entries(mapped.diagram.nodes)
    .filter(([nodeId, node]) => node.region === region && !shellPinIds.has(nodeId))
    .map(([nodeId]) => nodeId)
  const boundary = new Set(definition.boundary)
  const wires = [...new Set(
    Object.keys(definition.diagram.wires)
      .filter((wireId) =>
        !boundary.has(wireId)
        && derivedScope(definition.diagram, wireId, definition.boundary) === definitionRoot)
      .map((wireId) => mapped.wireMap.get(wireId)!),
  )]
  const selection = mkSelection(mapped.diagram, {
    region,
    regions,
    nodes,
    wires,
  })
  return extractSubgraph(mapped.diagram, selection)
}

function boundaryPins(
  extraction: ReturnType<typeof extractSubgraph>,
  args: readonly WireId[],
): readonly WireId[] {
  const pins: WireId[] = []
  for (const wireId of new Set(args)) {
    const boundaryIndex = extraction.attachments.indexOf(wireId)
    if (boundaryIndex === -1) {
      throw new RuleError(
        `fold: argument wire '${wireId}' is not one of the occurrence's attachment wires`,
      )
    }
    pins.push(extraction.pattern.boundary[boundaryIndex]!)
  }
  return pins
}

/**
 * Replace an exact boundary-pinned occurrence of a stored definition with one
 * reference. The definition ID selects both the graph to recognize and the
 * signature of the created ref.
 */
export function applyFold(
  diagram: Diagram,
  occurrence: SubgraphSelection,
  args: readonly WireId[],
  defId: string,
  definitions: ReadonlyMap<string, DiagramWithBoundary>,
  reservation?: IdReservation,
): Diagram {
  const definition = definitionAt(definitions, defId, 'fold')
  const sig = definitionSig(definition)
  if (args.length !== sig.args.length) {
    throw new RuleError(
      `fold: definition '${defId}' has signature '${sigKey(sig)}' `
      + `but ${args.length} argument wires were given`,
    )
  }
  args.forEach((wireId, index) => {
    const wire = diagram.wires[wireId]
    if (wire === undefined) throw new DiagramError(`unknown wire '${wireId}'`)
    if (!sigEquals(wire.sig, sig.args[index]!)) {
      throw new RuleError(
        `fold: argument wire '${wireId}' signature '${sigKey(wire.sig)}' `
        + `does not match definition '${defId}' argument ${index} signature '${sigKey(sig.args[index]!)}'`,
      )
    }
  })

  const extracted = extractSubgraph(diagram, occurrence)
  const argumentWires = new Set(args)
  for (const attachment of extracted.attachments) {
    if (!argumentWires.has(attachment)) {
      throw new RuleError(
        `fold: attachment wire '${attachment}' is not used by any argument position`,
      )
    }
  }

  const actualPins = boundaryPins(extracted, args)
  const expected = expectedFoldOccurrence(
    diagram,
    occurrence.region,
    args,
    definition,
  )
  const expectedPins = boundaryPins(expected, args)
  if (exploreForm(extracted.pattern.diagram, actualPins)
      !== exploreForm(expected.pattern.diagram, expectedPins)) {
    throw new RuleError(
      `fold: the occurrence does not match the definition `
      + `(boundary-pinned canonical forms differ)`,
    )
  }

  const cleaned = { root: diagram.root, ...removeSubgraphParts(diagram, occurrence) }
  const nodeId = freshId(new Set(Object.keys(diagram.nodes)), 'fold', reservation?.nodes)
  const ref: DiagramNode = {
    kind: 'ref',
    region: occurrence.region,
    defId,
    sig,
  }
  const nodes: Record<NodeId, DiagramNode> = { ...cleaned.nodes, [nodeId]: ref }
  const regions: Record<string, Region> = { ...cleaned.regions }
  const wires: Record<WireId, Wire> = {}
  for (const [id, wire] of Object.entries(cleaned.wires)) {
    const added = args.flatMap((argument, index): Endpoint[] =>
      argument === id ? [{ node: nodeId, port: { kind: 'arg', index } }] : [])
    wires[id] = added.length === 0
      ? wire
      : { sig: wire.sig, endpoints: [...wire.endpoints, ...added] }
  }
  // An argument wire whose other mentions all lived inside the folded
  // occurrence keeps its scope through the ref's port, but may be an end
  // short — complete it there (its derived scope is unchanged: occurrence
  // content sits at-or-under the fold region).
  const parts = { regions, nodes, wires }
  for (const argument of new Set(args)) {
    completeWireEnds(parts, argument, derivedScope(diagram, argument), 'fold', reservation?.nodes)
  }
  return mkDiagram({ root: cleaned.root, ...parts })
}
