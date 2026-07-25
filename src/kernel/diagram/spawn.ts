import type { Term } from '../term/term'
import { freePorts } from '../term/term'
import type { Diagram, DiagramNode, NodeId, Port, RegionId, Wire, WireId } from './diagram'
import { DiagramError, mkDiagram, portSig, requiredPorts } from './diagram'
import type { RelSig } from './sig'
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
  const ports: Port[] = requiredPorts(termNode)
  for (const port of ports) {
    const wire = freshId(takenWires, 'w', reservation?.wires)
    takenWires.add(wire)
    wires[wire] = { scope: region, sig: portSig(termNode, port), endpoints: [{ node, port }] }
  }
  return { node, diagram: mkDiagram({ root: d.root, regions: { ...d.regions }, nodes, wires }) }
}

export function spawnRelationNode(
  d: Diagram,
  region: RegionId,
  defId: string,
  sig: RelSig,
  reservation?: IdReservation,
): { diagram: Diagram; node: NodeId } {
  const node = freshId(new Set(Object.keys(d.nodes)), 'n', reservation?.nodes)
  const ref: DiagramNode = { kind: 'ref', region, defId, sig }
  const nodes: Record<NodeId, DiagramNode> = { ...d.nodes, [node]: ref }
  const wires: Record<WireId, Wire> = { ...d.wires }
  const takenWires = new Set(Object.keys(d.wires))
  for (const port of requiredPorts(ref)) {
    const wire = freshId(takenWires, 'w', reservation?.wires)
    takenWires.add(wire)
    wires[wire] = { scope: region, sig: portSig(ref, port), endpoints: [{ node, port }] }
  }
  return { node, diagram: mkDiagram({ root: d.root, regions: { ...d.regions }, nodes, wires }) }
}

/**
 * Spawns a fresh atom bound to an existing relational wire: the atom's sig is
 * read from the wire (`wireId`), its head port becomes a new endpoint on that
 * wire, and fresh arg wires are created from `sig.args`. `wireId` names a line
 * of identity, not an old-model binder region — any relational wire enclosing
 * `region` qualifies (mkDiagram enforces scope-encloses-region on the modified wire).
 */
export function spawnBoundRelationNode(
  d: Diagram,
  region: RegionId,
  wireId: WireId,
  reservation?: IdReservation,
): { diagram: Diagram; node: NodeId } {
  const target = d.wires[wireId]
  if (target === undefined) {
    throw new DiagramError(`spawnBoundRelationNode: wire '${wireId}' does not exist`)
  }
  if (target.sig.kind !== 'rel') {
    throw new DiagramError(`spawnBoundRelationNode: wire '${wireId}' has sig 'iota', expected a relation signature`)
  }
  const sig = target.sig
  const node = freshId(new Set(Object.keys(d.nodes)), 'n', reservation?.nodes)
  const atom: DiagramNode = { kind: 'atom', region, sig }
  const nodes: Record<NodeId, DiagramNode> = { ...d.nodes, [node]: atom }
  const wires: Record<WireId, Wire> = { ...d.wires }
  const takenWires = new Set(Object.keys(d.wires))
  wires[wireId] = { scope: target.scope, sig: target.sig, endpoints: [...target.endpoints, { node, port: { kind: 'head' } }] }
  for (let index = 0; index < sig.args.length; index++) {
    const wire = freshId(takenWires, 'w', reservation?.wires)
    takenWires.add(wire)
    wires[wire] = { scope: region, sig: sig.args[index]!, endpoints: [{ node, port: { kind: 'arg', index } }] }
  }
  return { node, diagram: mkDiagram({ root: d.root, regions: { ...d.regions }, nodes, wires }) }
}
