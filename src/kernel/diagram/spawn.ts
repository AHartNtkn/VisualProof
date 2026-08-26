import type { Diagram, DiagramNode, Endpoint, NodeId, RegionId, Wire, WireId } from './diagram'
import { DiagramError, mkDiagram, portSig, requiredPorts } from './diagram'
import { derivedScope, wireVisibleAt } from './regions'
import type { RelSig, Sig } from './sig'
import type { Term } from '../term/term'
import { freshId, type IdNamespaceReservation, type IdReservation } from './subgraph/freshId'

export function spawnTermNode(
  diagram: Diagram,
  region: RegionId,
  term: Term,
  interfaceArity: number,
  reservation?: IdReservation,
): { readonly diagram: Diagram; readonly node: NodeId; readonly wires: readonly WireId[] } {
  const takenNodes = new Set(Object.keys(diagram.nodes))
  const node = freshId(takenNodes, 'n', reservation?.nodes)
  takenNodes.add(node)
  const termNode: DiagramNode = { kind: 'term', region, term, freeArity: interfaceArity }
  const nodes: Record<NodeId, DiagramNode> = { ...diagram.nodes, [node]: termNode }
  const wires: Record<WireId, Wire> = { ...diagram.wires }
  const takenWires = new Set(Object.keys(diagram.wires))
  const spawnedWires: WireId[] = []
  for (const port of requiredPorts(termNode)) {
    const wire = freshId(takenWires, 'w', reservation?.wires)
    takenWires.add(wire)
    spawnedWires.push(wire)
    const wireSig = portSig(termNode, port)
    wires[wire] = {
      sig: wireSig,
      endpoints: [
        { node, port },
        mintPin(nodes, takenNodes, region, wireSig, reservation?.nodes),
      ],
    }
  }
  return {
    node,
    wires: Object.freeze(spawnedWires),
    diagram: mkDiagram({
      root: diagram.root,
      regions: { ...diagram.regions },
      nodes,
      wires,
    }),
  }
}

/**
 * Every spawned wire is born with its second end: a pin at the spawn
 * region, which is exactly where the old free tip read its quantifier.
 */
function mintPin(
  nodes: Record<NodeId, DiagramNode>,
  taken: Set<string>,
  region: RegionId,
  sig: Sig,
  reservation?: IdNamespaceReservation,
): Endpoint {
  const node = freshId(taken, 'pin', reservation)
  taken.add(node)
  nodes[node] = { kind: 'identity', region, sig, arity: 1 }
  return { node, port: { kind: 'identity', index: 0 } }
}

export function spawnRefNode(
  diagram: Diagram,
  region: RegionId,
  defId: string,
  sig: RelSig,
  reservation?: IdReservation,
): { diagram: Diagram; node: NodeId } {
  const takenNodes = new Set(Object.keys(diagram.nodes))
  const node = freshId(takenNodes, 'n', reservation?.nodes)
  takenNodes.add(node)
  const ref: DiagramNode = { kind: 'ref', region, defId, sig }
  const nodes: Record<NodeId, DiagramNode> = { ...diagram.nodes, [node]: ref }
  const wires: Record<WireId, Wire> = { ...diagram.wires }
  const takenWires = new Set(Object.keys(diagram.wires))
  for (const port of requiredPorts(ref)) {
    const wire = freshId(takenWires, 'w', reservation?.wires)
    takenWires.add(wire)
    const wireSig = portSig(ref, port)
    wires[wire] = {
      sig: wireSig,
      endpoints: [
        { node, port },
        mintPin(nodes, takenNodes, region, wireSig, reservation?.nodes),
      ],
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
  // Attaching a head at a region outside the wire's scope would silently
  // raise its quantifier to the DCA — quantifier movement is join/sever.
  if (!wireVisibleAt(diagram, wireId, region)) {
    throw new DiagramError(
      `spawnAtomNode: wire '${wireId}' scoped at '${derivedScope(diagram, wireId)}' `
      + `does not enclose spawn region '${region}'`,
    )
  }
  const takenNodes = new Set(Object.keys(diagram.nodes))
  const node = freshId(takenNodes, 'n', reservation?.nodes)
  takenNodes.add(node)
  const atom: DiagramNode = { kind: 'atom', region, sig: target.sig }
  const nodes: Record<NodeId, DiagramNode> = { ...diagram.nodes, [node]: atom }
  const wires: Record<WireId, Wire> = { ...diagram.wires }
  const takenWires = new Set(Object.keys(diagram.wires))
  wires[wireId] = {
    sig: target.sig,
    endpoints: [...target.endpoints, { node, port: { kind: 'head' } }],
  }
  for (let index = 0; index < target.sig.args.length; index += 1) {
    const wire = freshId(takenWires, 'w', reservation?.wires)
    takenWires.add(wire)
    const wireSig = target.sig.args[index]!
    wires[wire] = {
      sig: wireSig,
      endpoints: [
        { node, port: { kind: 'arg', index } },
        mintPin(nodes, takenNodes, region, wireSig, reservation?.nodes),
      ],
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
