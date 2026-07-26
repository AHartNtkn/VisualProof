import type { DiagramWithBoundary } from '../diagram/boundary'
import { exploreForm } from '../diagram/canonical/explore'
import type {
  Diagram,
  NodeId,
  Port,
  RegionId,
  WireId,
} from '../diagram/diagram'
import { portKey } from '../diagram/diagram'
import { sigEquals } from '../diagram/sig'
import { extractSubgraph } from '../diagram/subgraph/extract'
import type { SubgraphSelection } from '../diagram/subgraph/selection'

function directCuts(
  diagram: Diagram,
  parent: RegionId,
): readonly RegionId[] {
  return Object.entries(diagram.regions)
    .filter(([, region]) =>
      region.kind === 'cut' && region.parent === parent)
    .map(([id]) => id)
    .sort()
}

function directNodes(
  diagram: Diagram,
  region: RegionId,
): readonly NodeId[] {
  return Object.entries(diagram.nodes)
    .filter(([, node]) => node.region === region)
    .map(([id]) => id)
    .sort()
}

function scopedWires(
  diagram: Diagram,
  region: RegionId,
): readonly WireId[] {
  return Object.entries(diagram.wires)
    .filter(([, wire]) => wire.scope === region)
    .map(([id]) => id)
    .sort()
}

function wireAt(
  diagram: Diagram,
  node: NodeId,
  port: Port,
): WireId | undefined {
  const key = portKey(port)
  const matches = Object.entries(diagram.wires)
    .filter(([, wire]) => wire.endpoints.some((endpoint) =>
      endpoint.node === node && portKey(endpoint.port) === key))
    .map(([id]) => id)
  return matches.length === 1 ? matches[0] : undefined
}

function witnessArguments(
  diagram: Diagram,
  nodeId: NodeId,
  witness: WireId,
): readonly WireId[] | undefined {
  const node = diagram.nodes[nodeId]
  const witnessSig = diagram.wires[witness]?.sig
  if (
    node?.kind !== 'atom'
    || witnessSig?.kind !== 'rel'
    || !sigEquals(node.sig, witnessSig)
    || wireAt(diagram, nodeId, { kind: 'head' }) !== witness
  ) return undefined

  const args: WireId[] = []
  for (let index = 0; index < witnessSig.args.length; index += 1) {
    const wire = wireAt(diagram, nodeId, { kind: 'arg', index })
    if (wire === undefined) return undefined
    args.push(wire)
  }
  return args
}

function materialSelection(
  diagram: Diagram,
  region: RegionId,
  excludedRegion?: RegionId,
): SubgraphSelection {
  return {
    region,
    regions: directCuts(diagram, region)
      .filter((candidate) => candidate !== excludedRegion),
    nodes: directNodes(diagram, region),
    wires: scopedWires(diagram, region),
  }
}

function materialKey(
  diagram: Diagram,
  selection: SubgraphSelection,
  environment: readonly WireId[],
  required: readonly WireId[],
): string | undefined {
  const extracted = extractSubgraph(diagram, selection)
  if (
    extracted.attachments.some((wire) => !environment.includes(wire))
    || required.some((wire) => !extracted.attachments.includes(wire))
  ) {
    return undefined
  }
  const used = environment.map((wire) =>
    extracted.attachments.includes(wire))
  if (extracted.attachments.length !== used.filter(Boolean).length) {
    return undefined
  }
  const pins = environment.flatMap((wire) => {
    const index = extracted.attachments.indexOf(wire)
    return index === -1 ? [] : [extracted.pattern.boundary[index]!]
  })
  return `${used.map((value) => value ? '1' : '0').join('')}:`
    + exploreForm(extracted.pattern.diagram, pins)
}

function sameIds(
  actual: readonly string[],
  expected: readonly string[],
): boolean {
  return actual.length === expected.length
    && actual.every((id, index) => id === expected[index])
}

/**
 * Recognize the checked graph grammar
 * `forall args. P(args) <-> S(args)`.
 *
 * The first definition boundary is the fresh relation witness P; every
 * remaining boundary is a captured parameter used by both copies of S. A
 * matching stored definition therefore carries constructive witness existence
 * when its ref is spawned.
 */
export function isExactReificationDefinition(
  definition: DiagramWithBoundary,
): boolean {
  try {
    const { diagram, boundary } = definition
    if (
      boundary.length === 0
      || new Set(boundary).size !== boundary.length
    ) return false
    const witness = boundary[0]!
    const captures = boundary.slice(1)
    const witnessWire = diagram.wires[witness]
    if (
      witnessWire?.scope !== diagram.root
      || witnessWire.sig.kind !== 'rel'
      || boundary.some((wire) => diagram.wires[wire]?.scope !== diagram.root)
    ) return false

    const rootWires = scopedWires(diagram, diagram.root)
    if (!sameIds(rootWires, [...boundary].sort())) return false
    if (directNodes(diagram, diagram.root).length !== 0) return false

    let body = diagram.root
    let variableScope: RegionId | undefined
    if (witnessWire.sig.args.length > 0) {
      const universal = directCuts(diagram, diagram.root)
      if (universal.length !== 1) return false
      variableScope = universal[0]!
      if (directNodes(diagram, variableScope).length !== 0) return false
      const universalBody = directCuts(diagram, variableScope)
      if (universalBody.length !== 1) return false
      body = universalBody[0]!
    }

    const implications = directCuts(diagram, body)
    if (
      implications.length !== 2
      || directNodes(diagram, body).length !== 0
      || (
        body !== diagram.root
        && scopedWires(diagram, body).length !== 0
      )
    ) return false

    for (const forward of implications) {
      const reverse = implications.find((candidate) => candidate !== forward)!
      for (const forwardConsequent of directCuts(diagram, forward)) {
        const forwardNodes = directNodes(diagram, forward)
        if (
          forwardNodes.length !== 1
          || !sameIds(directCuts(diagram, forward), [forwardConsequent])
          || scopedWires(diagram, forward).length !== 0
        ) continue
        const variables = witnessArguments(
          diagram,
          forwardNodes[0]!,
          witness,
        )
        if (
          variables === undefined
          || new Set(variables).size !== variables.length
          || variables.length !== witnessWire.sig.args.length
        ) continue
        if (variableScope === undefined) {
          if (variables.length !== 0) continue
        } else {
          if (
            variables.some((wire, index) =>
              diagram.wires[wire]?.scope !== variableScope
              || !sigEquals(
                diagram.wires[wire]!.sig,
                witnessWire.sig.kind === 'rel'
                  ? witnessWire.sig.args[index]!
                  : witnessWire.sig,
              ))
            || !sameIds(
              scopedWires(diagram, variableScope),
              [...variables].sort(),
            )
          ) continue
        }

        for (const reverseConsequent of directCuts(diagram, reverse)) {
          const consequentNodes = directNodes(diagram, reverseConsequent)
          if (
            consequentNodes.length !== 1
            || directCuts(diagram, reverseConsequent).length !== 0
            || scopedWires(diagram, reverseConsequent).length !== 0
          ) continue
          const reverseVariables = witnessArguments(
            diagram,
            consequentNodes[0]!,
            witness,
          )
          if (
            reverseVariables === undefined
            || !sameIds(reverseVariables, variables)
          ) continue
          const witnessNodes = new Set([
            forwardNodes[0]!,
            consequentNodes[0]!,
          ])
          if (
            witnessWire.endpoints.length !== 2
            || witnessWire.endpoints.some((endpoint) =>
              endpoint.port.kind !== 'head'
              || !witnessNodes.has(endpoint.node))
          ) continue

          const environment = [...variables, ...captures]
          const forwardMaterial = materialKey(
            diagram,
            materialSelection(diagram, forwardConsequent),
            environment,
            captures,
          )
          const reverseMaterial = materialKey(
            diagram,
            materialSelection(
              diagram,
              reverse,
              reverseConsequent,
            ),
            environment,
            captures,
          )
          if (
            forwardMaterial !== undefined
            && forwardMaterial === reverseMaterial
          ) return true
        }
      }
    }
    return false
  } catch {
    return false
  }
}
