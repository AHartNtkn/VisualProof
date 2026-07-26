import type { Diagram, DiagramNode, Endpoint, NodeId, Region, Wire, WireId } from '../diagram/diagram'
import { DiagramError, mkDiagram, mkDiagramNormalized } from '../diagram/diagram'
import type { DiagramWithBoundary } from '../diagram/boundary'
import { mkDiagramWithBoundary } from '../diagram/boundary'
import { exploreForm } from '../diagram/canonical/explore'
import type { RelSig } from '../diagram/sig'
import { relSig, sigEquals, sigKey } from '../diagram/sig'
import { extractSubgraph } from '../diagram/subgraph/extract'
import { freshId, type IdReservation } from '../diagram/subgraph/freshId'
import type { SubgraphSelection } from '../diagram/subgraph/selection'
import { removeSubgraph, spliceSubgraphMapped } from '../diagram/subgraph/splice'
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
 * Merge definition boundary positions that the fold arguments identify, while
 * also respecting repeated incidences of one intrinsic definition wire.
 * Boundary classes remain ordered by first occurrence.
 */
function diagonalize(
  definition: DiagramWithBoundary,
  aliasPattern: readonly number[],
): DiagramWithBoundary {
  if (aliasPattern.length !== definition.boundary.length) {
    throw new DiagramError(
      `alias pattern length ${aliasPattern.length} does not match relation arity ${definition.boundary.length}`,
    )
  }

  const parent = aliasPattern.map((_, index) => index)
  const find = (index: number): number =>
    parent[index] === index ? index : (parent[index] = find(parent[index]!))
  const unite = (left: number, right: number): void => {
    const leftRoot = find(left)
    const rightRoot = find(right)
    if (leftRoot !== rightRoot) parent[rightRoot] = leftRoot
  }
  const firstLabel = new Map<number, number>()
  const firstWire = new Map<WireId, number>()
  aliasPattern.forEach((label, index) => {
    const labelPosition = firstLabel.get(label)
    if (labelPosition === undefined) firstLabel.set(label, index)
    else unite(labelPosition, index)

    const wire = definition.boundary[index]!
    const wirePosition = firstWire.get(wire)
    if (wirePosition === undefined) firstWire.set(wire, index)
    else unite(wirePosition, index)
  })

  const classes: number[][] = []
  const classIndex = new Map<number, number>()
  aliasPattern.forEach((_, index) => {
    const root = find(index)
    let target = classIndex.get(root)
    if (target === undefined) {
      target = classes.length
      classIndex.set(root, target)
      classes.push([])
    }
    classes[target]!.push(index)
  })

  const endpoints: Record<WireId, Endpoint[]> = {}
  for (const [id, wire] of Object.entries(definition.diagram.wires)) {
    endpoints[id] = [...wire.endpoints]
  }
  const boundary: WireId[] = []
  for (const positions of classes) {
    const representative = definition.boundary[positions[0]!]!
    boundary.push(representative)
    const members = [...new Set(positions.map((index) => definition.boundary[index]!))]
    for (const member of members) {
      if (member === representative) continue
      endpoints[representative]!.push(...endpoints[member]!)
      delete endpoints[member]
    }
  }

  const wires: Record<WireId, Wire> = {}
  for (const [id, wireEndpoints] of Object.entries(endpoints)) {
    const source = definition.diagram.wires[id]!
    wires[id] = { scope: source.scope, sig: source.sig, endpoints: wireEndpoints }
  }
  const normalized = mkDiagramNormalized({
    root: definition.diagram.root,
    regions: { ...definition.diagram.regions },
    nodes: { ...definition.diagram.nodes },
    wires,
  })
  const normalizedBoundary = boundary.map((wire) => {
    const image = normalized.wireImage.get(wire)
    if (image === undefined) {
      throw new DiagramError(
        `normalization removed definition boundary wire '${wire}' without a surviving image`,
      )
    }
    return image
  })
  return mkDiagramWithBoundary(normalized.diagram, normalizedBoundary)
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

  const { pattern, attachments } = extractSubgraph(diagram, occurrence)
  const classOf = new Map<WireId, number>()
  const aliasPattern = args.map((wire) => {
    let label = classOf.get(wire)
    if (label === undefined) {
      label = classOf.size
      classOf.set(wire, label)
    }
    return label
  })
  for (const attachment of attachments) {
    if (!classOf.has(attachment)) {
      throw new RuleError(
        `fold: attachment wire '${attachment}' is not used by any argument position`,
      )
    }
  }

  const distinctArgs = [...classOf.keys()]
  const reordered = distinctArgs.map((wire) => {
    const index = attachments.indexOf(wire)
    if (index === -1) {
      throw new RuleError(
        `fold: argument wire '${wire}' is not one of the occurrence's attachment wires`,
      )
    }
    return pattern.boundary[index]!
  })
  const expected = diagonalize(definition, aliasPattern)
  if (exploreForm(pattern.diagram, reordered)
      !== exploreForm(expected.diagram, expected.boundary)) {
    throw new RuleError(
      `fold: the occurrence does not match the definition `
      + `(boundary-pinned canonical forms differ)`,
    )
  }

  const cleaned = removeSubgraph(diagram, occurrence)
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
      : { scope: wire.scope, sig: wire.sig, endpoints: [...wire.endpoints, ...added] }
  }
  return mkDiagram({ root: cleaned.root, regions, nodes, wires })
}
