import type { Diagram, DiagramNode, NodeId, RegionId, Wire, WireId } from './diagram'
import { DiagramError, mkDiagram, portSig, requiredPorts } from './diagram'
import type { RelSig } from './sig'
import { freshId, type IdReservation } from './subgraph/freshId'

export function spawnRefNode(
  diagram: Diagram,
  region: RegionId,
  defId: string,
  sig: RelSig,
  reservation?: IdReservation,
): { diagram: Diagram; node: NodeId } {
  const node = freshId(new Set(Object.keys(diagram.nodes)), 'n', reservation?.nodes)
  const ref: DiagramNode = { kind: 'ref', region, defId, sig }
  const nodes: Record<NodeId, DiagramNode> = { ...diagram.nodes, [node]: ref }
  const wires: Record<WireId, Wire> = { ...diagram.wires }
  const takenWires = new Set(Object.keys(diagram.wires))
  for (const port of requiredPorts(ref)) {
    const wire = freshId(takenWires, 'w', reservation?.wires)
    takenWires.add(wire)
    wires[wire] = {
      scope: region,
      sig: portSig(ref, port),
      endpoints: [{ node, port }],
    }
  }
  return {
    node,
    diagram: mkDiagram({
      root: diagram.root,
      regions: { ...diagram.regions },
      nodes,
      wires,
    }),
  }
}

/** Bind a fresh atom head to one existing relational wire. */
export function spawnAtomNode(
  diagram: Diagram,
  region: RegionId,
  wireId: WireId,
  reservation?: IdReservation,
): { diagram: Diagram; node: NodeId } {
  const target = diagram.wires[wireId]
  if (target === undefined) {
    throw new DiagramError(`spawnAtomNode: wire '${wireId}' does not exist`)
  }
  if (target.sig.kind !== 'rel') {
    throw new DiagramError(
      `spawnAtomNode: wire '${wireId}' has sig 'iota', expected a relation signature`,
    )
  }
  const node = freshId(new Set(Object.keys(diagram.nodes)), 'n', reservation?.nodes)
  const atom: DiagramNode = { kind: 'atom', region, sig: target.sig }
  const nodes: Record<NodeId, DiagramNode> = { ...diagram.nodes, [node]: atom }
  const wires: Record<WireId, Wire> = { ...diagram.wires }
  const takenWires = new Set(Object.keys(diagram.wires))
  wires[wireId] = {
    scope: target.scope,
    sig: target.sig,
    endpoints: [...target.endpoints, { node, port: { kind: 'head' } }],
  }
  for (let index = 0; index < target.sig.args.length; index += 1) {
    const wire = freshId(takenWires, 'w', reservation?.wires)
    takenWires.add(wire)
    wires[wire] = {
      scope: region,
      sig: target.sig.args[index]!,
      endpoints: [{ node, port: { kind: 'arg', index } }],
    }
  }
  return {
    node,
    diagram: mkDiagram({
      root: diagram.root,
      regions: { ...diagram.regions },
      nodes,
      wires,
    }),
  }
}
