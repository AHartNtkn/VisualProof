import type { Diagram, Endpoint, NodeId, WireId } from '../diagram'
import { endpointPositionKey } from '../diagram'

function sameSortedValues(
  expected: readonly string[],
  actual: readonly string[],
): boolean {
  return expected.length === actual.length
    && expected.every((value, index) => value === actual[index])
}

/** Compare a mapped endpoint multiset with an exact or open-boundary image. */
export function mappedEndpointsMatch(
  sourceDiagram: Diagram,
  sourceEndpoints: readonly Endpoint[],
  targetDiagram: Diagram,
  targetEndpoints: readonly Endpoint[],
  nodeImage: (node: NodeId) => NodeId,
  allowTargetExtras: boolean,
): boolean {
  const expected = sourceEndpoints.map((endpoint) => JSON.stringify([
    nodeImage(endpoint.node),
    endpointPositionKey(sourceDiagram, endpoint),
  ])).sort()
  const actual = targetEndpoints.map((endpoint) => JSON.stringify([
    endpoint.node,
    endpointPositionKey(targetDiagram, endpoint),
  ])).sort()
  if (!allowTargetExtras) return sameSortedValues(expected, actual)

  const remaining = [...actual]
  for (const value of expected) {
    const index = remaining.indexOf(value)
    if (index < 0) return false
    remaining.splice(index, 1)
  }
  return true
}

/** Compare unordered wire-incidence multisets after transporting source IDs. */
export function mappedWireIncidencesMatch(
  sourceWires: readonly WireId[],
  targetWires: readonly WireId[],
  wireImage: (wire: WireId) => WireId,
): boolean {
  const expected = sourceWires.map(wireImage).sort()
  const actual = [...targetWires].sort()
  return sameSortedValues(expected, actual)
}
