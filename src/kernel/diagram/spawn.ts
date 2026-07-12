import type { Term } from '../term/term'
import { freePorts } from '../term/term'
import type { Diagram, DiagramNode, NodeId, Port, RegionId, Wire, WireId } from './diagram'
import { mkDiagram, requiredPorts } from './diagram'
import { freshId } from './subgraph/freshId'

export function spawnTermNode(d: Diagram, region: RegionId, term: Term): { diagram: Diagram; node: NodeId } {
  const node = freshId(new Set(Object.keys(d.nodes)), 'n')
  const nodes: Record<NodeId, DiagramNode> = { ...d.nodes, [node]: { kind: 'term', region, term } }
  const wires: Record<WireId, Wire> = { ...d.wires }
  const takenWires = new Set(Object.keys(d.wires))
  const ports: Port[] = [{ kind: 'output' }, ...freePorts(term).map((name): Port => ({ kind: 'freeVar', name }))]
  for (const port of ports) {
    const wire = freshId(takenWires, 'w')
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
): { diagram: Diagram; node: NodeId } {
  const node = freshId(new Set(Object.keys(d.nodes)), 'n')
  const ref: DiagramNode = { kind: 'ref', region, defId, arity }
  const nodes: Record<NodeId, DiagramNode> = { ...d.nodes, [node]: ref }
  const wires: Record<WireId, Wire> = { ...d.wires }
  const takenWires = new Set(Object.keys(d.wires))
  for (const port of requiredPorts(d, ref)) {
    const wire = freshId(takenWires, 'w')
    takenWires.add(wire)
    wires[wire] = { scope: region, endpoints: [{ node, port }] }
  }
  return { node, diagram: mkDiagram({ root: d.root, regions: { ...d.regions }, nodes, wires }) }
}

export function spawnBoundRelationNode(d: Diagram, region: RegionId, binder: RegionId): { diagram: Diagram; node: NodeId } {
  const node = freshId(new Set(Object.keys(d.nodes)), 'n')
  const atom: DiagramNode = { kind: 'atom', region, binder }
  const nodes: Record<NodeId, DiagramNode> = { ...d.nodes, [node]: atom }
  const wires: Record<WireId, Wire> = { ...d.wires }
  const takenWires = new Set(Object.keys(d.wires))
  for (const port of requiredPorts(d, atom)) {
    const wire = freshId(takenWires, 'w')
    takenWires.add(wire)
    wires[wire] = { scope: region, endpoints: [{ node, port }] }
  }
  return { node, diagram: mkDiagram({ root: d.root, regions: { ...d.regions }, nodes, wires }) }
}
