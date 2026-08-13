import type { Diagram, DiagramNode, Endpoint, Region, RegionId, Wire, WireId } from '../diagram'
import { DiagramError, mkDiagram } from '../diagram'
import { derivedScope, wireVisibleAt } from '../regions'
import type { DiagramWithBoundary } from '../boundary'
import { sigEquals, sigKey } from '../sig'
import type { SubgraphSelection } from './selection'
import { selectionContents } from './selection'
import {
  createIdMintRecorder,
  freezeIdMintLog,
  freshId,
  withIdMintCapture,
  type IdMintLog,
  type IdReservation,
} from './freshId'

export type SpliceOptions = {
  readonly reserved?: IdReservation | undefined
}

export type MappedSplice = {
  readonly diagram: Diagram
  /** Every region, node, and internal wire minted by this splice. */
  readonly allocation: IdMintLog
  readonly regionMap: ReadonlyMap<RegionId, RegionId>
  readonly nodeMap: ReadonlyMap<string, string>
  /** Internal wires map to fresh wires; boundary stubs map to their host attachment. */
  readonly wireMap: ReadonlyMap<WireId, WireId>
}

/** The removal as raw parts, for rules that repair before validating. */
export function removeSubgraphParts(d: Diagram, sel: SubgraphSelection): {
  regions: Record<RegionId, Region>
  nodes: Record<string, DiagramNode>
  wires: Record<WireId, Wire>
} {
  const c = selectionContents(d, sel)
  const internal = new Set(c.internalWires)
  const regions: Record<RegionId, Region> = {}
  for (const [id, r] of Object.entries(d.regions)) {
    if (!c.allRegions.has(id)) regions[id] = r
  }
  const nodes: Record<string, DiagramNode> = {}
  for (const [id, n] of Object.entries(d.nodes)) {
    if (!c.allNodes.has(id)) nodes[id] = n
  }
  const wires: Record<WireId, Wire> = {}
  for (const [id, w] of Object.entries(d.wires)) {
    if (internal.has(id)) continue
    wires[id] = {
      sig: w.sig,
      endpoints: w.endpoints.filter((ep) => !c.allNodes.has(ep.node)),
    }
  }
  return { regions, nodes, wires }
}

/** Drop the selection's content; touching wires keep only their outside endpoints. */
export function removeSubgraph(d: Diagram, sel: SubgraphSelection): Diagram {
  return mkDiagram({ root: d.root, ...removeSubgraphParts(d, sel) })
}

/**
 * Insert a pattern into a host region. Its ordered boundary incidences are
 * connected to the index-aligned host attachments. When several incidences
 * expose the same pattern wire but land on distinct host wires, splice
 * creates one local identity node at the application region; that explicit
 * equality PERSISTS until a recorded identification step absorbs it —
 * nothing rewrites it eagerly. Each boundary stub's endpoints are copied
 * exactly once onto its first ordered attachment. Pattern content gets
 * fresh host ids deterministically (ids are final: no rule renames a wire
 * it does not delete); the result is re-validated by mkDiagram.
 *
 * Landing a boundary stub onto a host wire requires their signatures to be
 * equal: the stub is a line of identity of a fixed sort, and it may only be
 * glued to a host line of the same sort. Every copied wire carries its
 * pattern signature.
 */
export function spliceSubgraphMapped(
  host: Diagram,
  atRegion: RegionId,
  pattern: DiagramWithBoundary,
  attachments: readonly WireId[],
  options: SpliceOptions = {},
): MappedSplice {
  if (host.regions[atRegion] === undefined) {
    throw new DiagramError(`splice region '${atRegion}' does not exist`)
  }
  if (attachments.length !== pattern.boundary.length) {
    throw new DiagramError(`expected ${pattern.boundary.length} attachments, got ${attachments.length}`)
  }
  const pd = pattern.diagram
  const allocation = createIdMintRecorder()
  const spliceReservation = withIdMintCapture(options.reserved, allocation)
  const boundarySet = new Set(pattern.boundary)
  pattern.boundary.forEach((stub, i) => {
    const a = attachments[i]!
    const w = host.wires[a]
    if (w === undefined) throw new DiagramError(`attachment wire '${a}' does not exist`)
    if (!wireVisibleAt(host, a, atRegion)) {
      throw new DiagramError(
        `attachment wire '${a}' (scope '${derivedScope(host, a)}') does not enclose splice region '${atRegion}'`,
      )
    }
    const stubSig = pd.wires[stub]!.sig
    if (!sigEquals(stubSig, w.sig)) {
      throw new DiagramError(
        `boundary stub '${stub}' (sig '${sigKey(stubSig)}') cannot land on attachment wire '${a}' (sig '${sigKey(w.sig)}')`,
      )
    }
  })

  // A repeated boundary identity is an equality constraint at the application
  // site, not permission to identify the host wires globally. Keep the first
  // ordered attachment as the copied pattern wire's representative and record
  // every distinct later attachment for one explicit local identity node
  // below. Repeating the same stub/attachment pair adds no new equality.
  const firstAttachmentOfStub = new Map<WireId, WireId>()
  const attachmentsOfStub = new Map<WireId, Set<WireId>>()
  pattern.boundary.forEach((stub, i) => {
    const attachment = attachments[i]!
    const first = firstAttachmentOfStub.get(stub)
    if (first === undefined) {
      firstAttachmentOfStub.set(stub, attachment)
      attachmentsOfStub.set(stub, new Set([attachment]))
    } else {
      const seen = attachmentsOfStub.get(stub)!
      if (!seen.has(attachment)) {
        seen.add(attachment)
      }
    }
  })

  // fresh-id maps for pattern regions (except root), nodes, internal wires
  const takenRegions = new Set(Object.keys(host.regions))
  const regionMap = new Map<RegionId, RegionId>([[pd.root, atRegion]])
  for (const id of Object.keys(pd.regions)) {
    if (id === pd.root) continue
    const fresh = freshId(takenRegions, id, spliceReservation.regions)
    takenRegions.add(fresh)
    regionMap.set(id, fresh)
  }
  const takenNodes = new Set(Object.keys(host.nodes))
  const nodeMap = new Map<string, string>()
  for (const id of Object.keys(pd.nodes)) {
    const fresh = freshId(takenNodes, id, spliceReservation.nodes)
    takenNodes.add(fresh)
    nodeMap.set(id, fresh)
  }
  const aliasNodes = [...attachmentsOfStub]
    .filter(([, attached]) => attached.size > 1)
    .map(([stub, attached]) => {
      const position = pattern.boundary.indexOf(stub)
      const fresh = freshId(takenNodes, `identity_${position}`, spliceReservation.nodes)
      takenNodes.add(fresh)
      return {
        id: fresh,
        sig: pd.wires[stub]!.sig,
        attachments: [...attached],
      }
    })
  // Mint against the full PRE-QUOTIENT namespace: a wire removed by the
  // pushout must never be resurrected as unrelated copied content.
  const takenWires = new Set(Object.keys(host.wires))
  const wireMap = new Map<WireId, WireId>()
  pattern.boundary.forEach((stub, index) => {
    if (!wireMap.has(stub)) wireMap.set(stub, attachments[index]!)
  })
  for (const id of Object.keys(pd.wires)) {
    if (boundarySet.has(id)) continue
    const fresh = freshId(takenWires, id, spliceReservation.wires)
    takenWires.add(fresh)
    wireMap.set(id, fresh)
  }

  const regions: Record<RegionId, Region> = { ...host.regions }
  for (const [id, r] of Object.entries(pd.regions)) {
    if (id === pd.root) continue
    const mapped = regionMap.get(id)!
    if (r.kind === 'sheet') continue // impossible: single sheet is the root
    regions[mapped] = { kind: 'cut', parent: regionMap.get(r.parent)! }
  }

  // Return-typed switch (no default): a new node kind forces its rebuild here.
  const rebuildNode = (n: DiagramNode): DiagramNode => {
    switch (n.kind) {
      case 'atom': return { kind: 'atom', region: regionMap.get(n.region)!, sig: n.sig }
      case 'ref': return { kind: 'ref', region: regionMap.get(n.region)!, defId: n.defId, sig: n.sig }
      case 'identity':
        return {
          kind: 'identity',
          region: regionMap.get(n.region)!,
          sig: n.sig,
          arity: n.arity,
        }
    }
  }
  const nodes: Record<string, DiagramNode> = { ...host.nodes }
  for (const [id, n] of Object.entries(pd.nodes)) {
    nodes[nodeMap.get(id)!] = rebuildNode(n)
  }
  for (const alias of aliasNodes) {
    nodes[alias.id] = {
      kind: 'identity',
      region: atRegion,
      sig: alias.sig,
      arity: alias.attachments.length,
    }
  }

  const mapEndpoints = (eps: readonly Endpoint[]): Endpoint[] =>
    eps.map((ep) => ({ node: nodeMap.get(ep.node)!, port: ep.port }))

  const wires: Record<WireId, Wire> = { ...host.wires }
  for (const [id, w] of Object.entries(pd.wires)) {
    if (boundarySet.has(id)) continue
    wires[wireMap.get(id)!] = {
      sig: w.sig,
      endpoints: mapEndpoints(w.endpoints),
    }
  }
  const copiedBoundary = new Set<WireId>()
  pattern.boundary.forEach((stubId, i) => {
    if (copiedBoundary.has(stubId)) return
    copiedBoundary.add(stubId)
    const hostWireId = attachments[i]!
    const stub = pd.wires[stubId]!
    const existing = wires[hostWireId]!
    wires[hostWireId] = {
      sig: existing.sig,
      endpoints: [...existing.endpoints, ...mapEndpoints(stub.endpoints)],
    }
  })
  for (const alias of aliasNodes) {
    alias.attachments.forEach((wireId, index) => {
      const wire = wires[wireId]!
      wires[wireId] = {
        sig: wire.sig,
        endpoints: [
          ...wire.endpoints,
          { node: alias.id, port: { kind: 'identity', index } },
        ],
      }
    })
  }

  return Object.freeze({
    diagram: mkDiagram({ root: host.root, regions, nodes, wires }),
    allocation: freezeIdMintLog(allocation),
    regionMap: new Map(regionMap),
    nodeMap: new Map(nodeMap),
    wireMap: new Map(wireMap),
  })
}

/** Ordinary convenience entry: canonical mapped splice without extra reservations. */
export function spliceSubgraph(
  host: Diagram,
  atRegion: RegionId,
  pattern: DiagramWithBoundary,
  attachments: readonly WireId[],
): Diagram {
  return spliceSubgraphMapped(host, atRegion, pattern, attachments).diagram
}
