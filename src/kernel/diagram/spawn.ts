import type { Term } from '../term/term'
import { freePorts } from '../term/term'
import type { Diagram, DiagramNode, NodeId, Port, RegionId, Wire, WireId } from './diagram'
import { mkDiagram, requiredPorts } from './diagram'
import { freshId, type IdReservation } from './subgraph/freshId'

export function spawnTermNode(
  d: Diagram,
  region: RegionId,
  term: Term,
  declaredFreePorts: readonly string[] = freePorts(term),
  reservation?: IdReservation,
): { diagram: Diagram; node: NodeId } {
  const node = freshId(new Set(Object.keys(d.nodes)), 'n', reservation?.nodes)
  const termNode: DiagramNode = { kind: 'term', region, term, freePorts: [...declaredFreePorts] }
  const nodes: Record<NodeId, DiagramNode> = { ...d.nodes, [node]: termNode }
  const wires: Record<WireId, Wire> = { ...d.wires }
  const takenWires = new Set(Object.keys(d.wires))
  const ports: Port[] = requiredPorts(d, termNode)
  for (const port of ports) {
    const wire = freshId(takenWires, 'w', reservation?.wires)
    takenWires.add(wire)
    wires[wire] = { scope: region, endpoints: [{ node, port }] }
  }
  return { node, diagram: mkDiagram({ root: d.root, regions: { ...d.regions }, nodes, wires }) }
}

export function spawnRelationNode(
  d: Diagram,
  region: RegionId,
  defId: string,
  arity: number,
  reservation?: IdReservation,
): { diagram: Diagram; node: NodeId } {
  const node = freshId(new Set(Object.keys(d.nodes)), 'n', reservation?.nodes)
  const ref: DiagramNode = { kind: 'ref', region, defId, arity }
  const nodes: Record<NodeId, DiagramNode> = { ...d.nodes, [node]: ref }
  const wires: Record<WireId, Wire> = { ...d.wires }
  const takenWires = new Set(Object.keys(d.wires))
  for (const port of requiredPorts(d, ref)) {
    const wire = freshId(takenWires, 'w', reservation?.wires)
    takenWires.add(wire)
    wires[wire] = { scope: region, endpoints: [{ node, port }] }
  }
  return { node, diagram: mkDiagram({ root: d.root, regions: { ...d.regions }, nodes, wires }) }
}

export function spawnBoundRelationNode(d: Diagram, region: RegionId, binder: RegionId, reservation?: IdReservation): { diagram: Diagram; node: NodeId } {
  const node = freshId(new Set(Object.keys(d.nodes)), 'n', reservation?.nodes)
  const atom: DiagramNode = { kind: 'atom', region, binder }
  const nodes: Record<NodeId, DiagramNode> = { ...d.nodes, [node]: atom }
  const wires: Record<WireId, Wire> = { ...d.wires }
  const takenWires = new Set(Object.keys(d.wires))
  for (const port of requiredPorts(d, atom)) {
    const wire = freshId(takenWires, 'w', reservation?.wires)
    takenWires.add(wire)
    wires[wire] = { scope: region, endpoints: [{ node, port }] }
  }
  return { node, diagram: mkDiagram({ root: d.root, regions: { ...d.regions }, nodes, wires }) }
}
