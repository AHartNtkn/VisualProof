export type {
  RegionId, NodeId, WireId, Region, DiagramNode, Port, Endpoint, Wire, Diagram,
} from './diagram'
export { mkDiagram, portKey, requiredPorts, DiagramError } from './diagram'
export { isAncestorOrEqual, cutDepth, polarity } from './regions'
export { DiagramBuilder } from './builder'
export { diagramToJson, diagramFromJson } from './json'
export type { DiagramWithBoundary } from './boundary'
export { mkDiagramWithBoundary, boundaryArity } from './boundary'
export { termShapeKey, positionalPortKey } from './canonical/shape'
export { canonicalForm } from './canonical/canonical'
export { diagramFingerprint, boundaryFingerprint, diagramsIsomorphic } from './canonical/fingerprint'
