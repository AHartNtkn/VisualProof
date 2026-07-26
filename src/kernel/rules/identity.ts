import type {
  Diagram,
  DiagramNode,
  NodeId,
  RegionId,
  Wire,
  WireId,
} from '../diagram/diagram'
import { DiagramError, mkDiagram } from '../diagram/diagram'
import { isAncestorOrEqual, polarity } from '../diagram/regions'
import { sigEquals, sigKey } from '../diagram/sig'
import { freshId, type IdReservation } from '../diagram/subgraph/freshId'
import { removeSubgraph } from '../diagram/subgraph/splice'
import { RuleError } from './error'

function wireAt(diagram: Diagram, wireId: WireId): Wire {
  const wire = diagram.wires[wireId]
  if (wire === undefined) throw new DiagramError(`unknown wire '${wireId}'`)
  return wire
}

function identityAt(diagram: Diagram, nodeId: NodeId, label: string): Extract<DiagramNode, { kind: 'identity' }> {
  const node = diagram.nodes[nodeId]
  if (node === undefined) throw new RuleError(`${label} '${nodeId}' does not name an identity node`)
  if (node.kind !== 'identity') {
    throw new RuleError(`${label} '${nodeId}' does not name an identity node`)
  }
  return node
}

function identityWireSet(diagram: Diagram, nodeId: NodeId): ReadonlySet<WireId> {
  return new Set(
    Object.entries(diagram.wires)
      .filter(([, wire]) => wire.endpoints.some((endpoint) => endpoint.node === nodeId))
      .map(([wireId]) => wireId),
  )
}

/**
 * Rule 4: insert one inherited identity in a negative region. Construction
 * delegates immediately to the canonical diagram owner, so an unconditional
 * same-scope identity collapses instead of surviving as a second authority.
 */
export function applyIdentityInsertion(
  diagram: Diagram,
  region: RegionId,
  wires: readonly WireId[],
  reservation?: IdReservation,
): Diagram {
  if (polarity(diagram, region) !== 'negative') {
    throw new RuleError('identity insertion requires a negative region')
  }
  if (wires.length < 2 || new Set(wires).size !== wires.length) {
    throw new RuleError('identity insertion requires at least two distinct wires')
  }

  const selected = wires.map((wireId) => [wireId, wireAt(diagram, wireId)] as const)
  const sig = selected[0]![1].sig
  for (const [wireId, wire] of selected) {
    if (!sigEquals(wire.sig, sig)) {
      throw new RuleError(
        `identity insertion wires must have the same signature; `
        + `'${wires[0]}' has '${sigKey(sig)}' but '${wireId}' has '${sigKey(wire.sig)}'`,
      )
    }
    if (!isAncestorOrEqual(diagram, wire.scope, region)) {
      throw new RuleError(
        `identity insertion wire '${wireId}' scoped at '${wire.scope}' is not visible at '${region}'`,
      )
    }
  }

  const nodeId = freshId(
    new Set(Object.keys(diagram.nodes)),
    'identity',
    reservation?.nodes,
  )
  const nodes: Record<NodeId, DiagramNode> = {
    ...diagram.nodes,
    [nodeId]: {
      kind: 'identity',
      region,
      sig,
      arity: wires.length,
    },
  }
  const rebuiltWires: Record<WireId, Wire> = { ...diagram.wires }
  wires.forEach((wireId, index) => {
    const wire = rebuiltWires[wireId]!
    rebuiltWires[wireId] = {
      scope: wire.scope,
      sig: wire.sig,
      endpoints: [
        ...wire.endpoints,
        { node: nodeId, port: { kind: 'identity', index } },
      ],
    }
  })

  return mkDiagram({
    root: diagram.root,
    regions: { ...diagram.regions },
    nodes,
    wires: rebuiltWires,
  })
}

export type IdentityContradictionEvidence = {
  readonly equality: NodeId
  readonly disequalityCut: RegionId
  readonly disequality: NodeId
}

function assertExactDisequalityChild(
  diagram: Diagram,
  disequalityCut: RegionId,
  disequality: NodeId,
): void {
  const inSubtree = (region: RegionId): boolean =>
    isAncestorOrEqual(diagram, disequalityCut, region)
  const extraRegion = Object.keys(diagram.regions)
    .some((region) => region !== disequalityCut && inSubtree(region))
  const extraNode = Object.entries(diagram.nodes)
    .some(([nodeId, node]) => nodeId !== disequality && inSubtree(node.region))
  const scopedWire = Object.values(diagram.wires)
    .some((wire) => inSubtree(wire.scope))
  if (extraRegion || extraNode || scopedWire) {
    throw new RuleError(
      `disequality cut '${disequalityCut}' must contain exactly the matching identity`,
    )
  }
}

/** Discover one exact asserted/directly-negated identity contradiction. */
export function findIdentityContradictionEvidence(
  diagram: Diagram,
  enclosingCut: RegionId,
): IdentityContradictionEvidence | null {
  const enclosing = diagram.regions[enclosingCut]
  if (enclosing === undefined || enclosing.kind !== 'cut') return null
  const equalities = Object.entries(diagram.nodes)
    .filter((entry): entry is [NodeId, Extract<DiagramNode, { kind: 'identity' }>] =>
      entry[1].kind === 'identity' && entry[1].region === enclosingCut)
    .sort(([left], [right]) => left.localeCompare(right))
  const childCuts = Object.entries(diagram.regions)
    .filter((entry): entry is [RegionId, Extract<Diagram['regions'][RegionId], { kind: 'cut' }>] =>
      entry[1].kind === 'cut' && entry[1].parent === enclosingCut)
    .sort(([left], [right]) => left.localeCompare(right))
  for (const [equality, equalityNode] of equalities) {
    const equalityWires = identityWireSet(diagram, equality)
    for (const [disequalityCut] of childCuts) {
      const disequalities = Object.entries(diagram.nodes)
        .filter((entry): entry is [NodeId, Extract<DiagramNode, { kind: 'identity' }>] =>
          entry[1].kind === 'identity' && entry[1].region === disequalityCut)
        .sort(([left], [right]) => left.localeCompare(right))
      for (const [disequality, disequalityNode] of disequalities) {
        if (!sigEquals(equalityNode.sig, disequalityNode.sig)) continue
        const disequalityWires = identityWireSet(diagram, disequality)
        if (
          equalityWires.size !== disequalityWires.size
          || [...equalityWires].some((wire) => !disequalityWires.has(wire))
        ) continue
        try {
          assertExactDisequalityChild(diagram, disequalityCut, disequality)
          return { equality, disequalityCut, disequality }
        } catch (error) {
          if (!(error instanceof RuleError)) throw error
        }
      }
    }
  }
  return null
}

/**
 * Rule 6: discharge an enclosing cut containing x=y together with a direct
 * child cut containing the same unordered identity. Every premise is graph
 * structure named by stable IDs; no object-language oracle participates.
 */
export function applyIdentityContradiction(
  diagram: Diagram,
  enclosingCut: RegionId,
  evidence: IdentityContradictionEvidence,
): Diagram {
  const enclosing = diagram.regions[enclosingCut]
  if (enclosing === undefined) throw new DiagramError(`unknown region '${enclosingCut}'`)
  if (enclosing.kind !== 'cut') {
    throw new RuleError(`identity contradiction requires a cut; '${enclosingCut}' is a sheet`)
  }

  const equality = identityAt(diagram, evidence.equality, 'equality evidence')
  if (equality.region !== enclosingCut) {
    throw new RuleError(
      `equality identity '${evidence.equality}' must be directly in enclosing cut '${enclosingCut}'`,
    )
  }

  const disequalityRegion = diagram.regions[evidence.disequalityCut]
  if (
    disequalityRegion === undefined
    || disequalityRegion.kind !== 'cut'
    || disequalityRegion.parent !== enclosingCut
  ) {
    throw new RuleError(
      `disequality cut '${evidence.disequalityCut}' must be a direct child of '${enclosingCut}'`,
    )
  }

  const disequality = identityAt(diagram, evidence.disequality, 'disequality evidence')
  if (disequality.region !== evidence.disequalityCut) {
    throw new RuleError(
      `disequality identity '${evidence.disequality}' must be directly in `
      + `disequality cut '${evidence.disequalityCut}'`,
    )
  }
  if (!sigEquals(equality.sig, disequality.sig)) {
    throw new RuleError(
      `identity contradiction nodes have different signatures `
      + `('${sigKey(equality.sig)}' and '${sigKey(disequality.sig)}')`,
    )
  }

  const equalityWires = identityWireSet(diagram, evidence.equality)
  const disequalityWires = identityWireSet(diagram, evidence.disequality)
  if (
    equalityWires.size !== disequalityWires.size
    || [...equalityWires].some((wireId) => !disequalityWires.has(wireId))
  ) {
    throw new RuleError('identity contradiction nodes have different attached wire sets')
  }
  assertExactDisequalityChild(
    diagram,
    evidence.disequalityCut,
    evidence.disequality,
  )

  return removeSubgraph(diagram, {
    region: enclosing.parent,
    regions: [enclosingCut],
    nodes: [],
    wires: [],
  })
}
