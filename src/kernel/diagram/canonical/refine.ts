import type { Diagram, DiagramNode, NodeId, Port, RegionId, WireId } from '../diagram'
import { DiagramError } from '../diagram'
import { sigKey } from '../sig'
import { serializeTerm } from '../../term/serialize'

/**
 * SHARED JOINT COLOR-REFINEMENT ENGINE.
 *
 * Generalizes the per-diagram individualization-refinement seed of
 * `explore.ts` to one or more diagrams ("sides") refined together: every
 * side's regions, nodes, and wires are colored by the same signature
 * vocabulary, so equal colors on different sides mean corresponding
 * structure. Signature strings never carry the side index — only the
 * content they describe — which is what makes cross-side colors
 * comparable. `Mark`s individualize specific elements before refinement by
 * folding a token into that element's initial signature; equal tokens on
 * different sides pair the marked elements across sides.
 */

export type Sort = 'region' | 'node' | 'wire'

/** One individualization: element `id` of `sides[side]` gets token `token`
 *  folded into its initial color. Two marks with equal tokens pair the
 *  marked elements across sides. */
export type Mark = {
  readonly side: number
  readonly sort: Sort
  readonly id: string
  readonly token: number
}

export type RefinementSide = {
  readonly diagram: Diagram
  readonly pins: readonly WireId[]
}

export type SideColors = {
  readonly region: ReadonlyMap<RegionId, number>
  readonly node: ReadonlyMap<NodeId, number>
  readonly wire: ReadonlyMap<WireId, number>
}

export type RefineIndex = {
  readonly regionIds: readonly RegionId[]
  readonly nodeIds: readonly NodeId[]
  readonly wireIds: readonly WireId[]
  readonly regionKindKey: ReadonlyMap<RegionId, string>
  readonly parentOf: ReadonlyMap<RegionId, RegionId | null>
  readonly childrenOf: ReadonlyMap<RegionId, readonly RegionId[]>
  readonly nodesIn: ReadonlyMap<RegionId, readonly NodeId[]>
  readonly nodeContentKey: ReadonlyMap<NodeId, string>
  readonly nodeRegion: ReadonlyMap<NodeId, RegionId>
  readonly nodePortOrder: ReadonlyMap<NodeId, readonly string[]>
  readonly nodePortWire: ReadonlyMap<NodeId, ReadonlyMap<string, WireId>>
  readonly identityIncidentWires: ReadonlyMap<NodeId, readonly WireId[]>
  readonly wireSigKey: ReadonlyMap<WireId, string>
  readonly wireEndpoints: ReadonlyMap<WireId, readonly { node: NodeId; pkey: string }[]>
  readonly pinOf: ReadonlyMap<WireId, readonly number[]>
}

function endpointKey(d: Diagram, node: NodeId, port: Port): string {
  const n = d.nodes[node]!
  switch (n.kind) {
    case 'term':
      if (port.kind === 'output') return 'out'
      if (port.kind === 'free') return `f${port.index}`
      throw new DiagramError(`term '${node}' cannot carry port '${port.kind}'`)
    case 'atom':
      if (port.kind === 'head') return 'hd'
      if (port.kind === 'arg') return `a${port.index}`
      throw new DiagramError(`atom '${node}' cannot carry port '${port.kind}'`)
    case 'ref':
      if (port.kind === 'arg') return `a${port.index}`
      throw new DiagramError(`ref '${node}' cannot carry port '${port.kind}'`)
    case 'identity':
      if (port.kind === 'identity') return 'i'
      throw new DiagramError(`identity '${node}' cannot carry port '${port.kind}'`)
  }
}

/**
 * Build one diagram's `RefineIndex`: a per-side lookup of content keys
 * (region kind, node signature/defId/arity, wire signature), port wiring
 * (each node's port-key-to-wire map, or an identity node's unordered
 * incident-wire list), and structural incidences (region parent/children,
 * nodes-in-region, wire endpoints with position keys, and pin positions).
 * Pure in `(d, pins)`, so a caller refining the same diagram under many
 * different `marks` builds this once and reuses it.
 */
export function buildRefineIndex(d: Diagram, pins: readonly WireId[]): RefineIndex {
  for (const w of pins) {
    if (d.wires[w] === undefined) throw new DiagramError(`pinned wire '${w}' does not exist`)
  }

  const regionIds = Object.keys(d.regions)
  const nodeIds = Object.keys(d.nodes)
  const wireIds = Object.keys(d.wires)

  const regionKindKey = new Map<RegionId, string>()
  const parentOf = new Map<RegionId, RegionId | null>()
  const childrenOf = new Map<RegionId, RegionId[]>()
  const nodesIn = new Map<RegionId, NodeId[]>()
  for (const id of regionIds) {
    childrenOf.set(id, [])
    nodesIn.set(id, [])
  }
  for (const id of regionIds) {
    const r = d.regions[id]!
    regionKindKey.set(id, r.kind)
    if (r.kind === 'sheet') {
      parentOf.set(id, null)
    } else {
      parentOf.set(id, r.parent)
      childrenOf.get(r.parent)!.push(id)
    }
  }

  const nodeContentKey = new Map<NodeId, string>()
  const nodeRegion = new Map<NodeId, RegionId>()
  const nodePortOrder = new Map<NodeId, string[]>()
  const nodePortWire = new Map<NodeId, Map<string, WireId>>()
  const identityIncidentWires = new Map<NodeId, WireId[]>()
  const nodeCanon = (n: DiagramNode): { contentKey: string; portOrder: string[] } => {
    switch (n.kind) {
      case 'term':
        return {
          contentKey: `term:${serializeTerm(n.term)}:${n.freeArity}`,
          portOrder: ['out', ...Array.from({ length: n.freeArity }, (_, i) => `f${i}`)],
        }
      case 'atom':
        return {
          contentKey: `atom|${sigKey(n.sig)}`,
          portOrder: ['hd', ...n.sig.args.map((_, i) => `a${i}`)],
        }
      case 'ref':
        return {
          contentKey: `ref:${n.defId}:${sigKey(n.sig)}`,
          portOrder: n.sig.args.map((_, i) => `a${i}`),
        }
      case 'identity':
        return {
          contentKey: `identity:${sigKey(n.sig)}:${n.arity}`,
          portOrder: [],
        }
    }
  }
  for (const id of nodeIds) {
    const n = d.nodes[id]!
    nodeRegion.set(id, n.region)
    nodesIn.get(n.region)!.push(id)
    nodePortWire.set(id, new Map())
    if (n.kind === 'identity') identityIncidentWires.set(id, [])
    const canon = nodeCanon(n)
    nodeContentKey.set(id, canon.contentKey)
    nodePortOrder.set(id, canon.portOrder)
  }

  const wireSigKey = new Map<WireId, string>()
  const wireEndpoints = new Map<WireId, { node: NodeId; pkey: string }[]>()
  for (const id of wireIds) {
    const w = d.wires[id]!
    wireSigKey.set(id, sigKey(w.sig))
    const eps = w.endpoints.map((ep) => {
      const pkey = endpointKey(d, ep.node, ep.port)
      if (d.nodes[ep.node]!.kind === 'identity') {
        identityIncidentWires.get(ep.node)!.push(id)
      } else {
        nodePortWire.get(ep.node)!.set(pkey, id)
      }
      return { node: ep.node, pkey }
    })
    wireEndpoints.set(id, eps)
  }

  const pinOf = new Map<WireId, number[]>()
  pins.forEach((w, i) => {
    const positions = pinOf.get(w)
    if (positions === undefined) pinOf.set(w, [i])
    else positions.push(i)
  })

  return {
    regionIds, nodeIds, wireIds, regionKindKey, parentOf, childrenOf, nodesIn,
    nodeContentKey, nodeRegion, nodePortOrder,
    nodePortWire, identityIncidentWires,
    wireSigKey, wireEndpoints, pinOf,
  }
}

type MutableColors = { region: Map<RegionId, number>; node: Map<NodeId, number>; wire: Map<WireId, number> }

function classCount(sides: readonly MutableColors[]): number {
  const all = new Set<number>()
  for (const c of sides) {
    for (const v of c.region.values()) all.add(v)
    for (const v of c.node.values()) all.add(v)
    for (const v of c.wire.values()) all.add(v)
  }
  return all.size
}

/** Rank distinct signatures jointly, across all sides' entries. */
function rankSignatures(entries: readonly [string, string][]): Map<string, number> {
  const distinct = [...new Set(entries.map(([, sig]) => sig))].sort()
  const rank = new Map(distinct.map((s, i) => [s, i]))
  const out = new Map<string, number>()
  for (const [key, sig] of entries) out.set(key, rank.get(sig)!)
  return out
}

function marksFor(marks: readonly Mark[], side: number, sort: Sort, id: string): readonly number[] {
  return marks
    .filter((m) => m.side === side && m.sort === sort && m.id === id)
    .map((m) => m.token)
    .sort((a, b) => a - b)
}

function withMarks(sig: string, tokens: readonly number[]): string {
  return tokens.length === 0 ? sig : `${sig}${tokens.map((t) => `|#${t}`).join('')}`
}

function initialColors(indexes: readonly RefineIndex[], marks: readonly Mark[]): MutableColors[] {
  const entries: [string, string][] = []
  indexes.forEach((idx, side) => {
    for (const id of idx.regionIds) {
      const sig = withMarks(`R|${idx.regionKindKey.get(id)!}`, marksFor(marks, side, 'region', id))
      entries.push([`${side}|R${id}`, sig])
    }
    for (const id of idx.nodeIds) {
      const sig = withMarks(`N|${idx.nodeContentKey.get(id)!}`, marksFor(marks, side, 'node', id))
      entries.push([`${side}|N${id}`, sig])
    }
    for (const id of idx.wireIds) {
      const pins = idx.pinOf.get(id)
      const base = `W|${pins === undefined ? 'w' : `pins${JSON.stringify(pins)}`}`
      const sig = withMarks(base, marksFor(marks, side, 'wire', id))
      entries.push([`${side}|W${id}`, sig])
    }
  })
  const ranked = rankSignatures(entries)
  return indexes.map((idx, side) => ({
    region: new Map(idx.regionIds.map((id) => [id, ranked.get(`${side}|R${id}`)!])),
    node: new Map(idx.nodeIds.map((id) => [id, ranked.get(`${side}|N${id}`)!])),
    wire: new Map(idx.wireIds.map((id) => [id, ranked.get(`${side}|W${id}`)!])),
  }))
}

function refineOnce(indexes: readonly RefineIndex[], sides: readonly MutableColors[]): MutableColors[] {
  const entries: [string, string][] = []
  indexes.forEach((idx, side) => {
    const c = sides[side]!
    for (const id of idx.regionIds) {
      const parent = idx.parentOf.get(id)
      const children = idx.childrenOf.get(id)!.map((x) => c.region.get(x)!).sort((a, b) => a - b)
      const nodes = idx.nodesIn.get(id)!.map((x) => c.node.get(x)!).sort((a, b) => a - b)
      const parentColor = parent == null ? '-' : String(c.region.get(parent)!)
      entries.push([`${side}|R${id}`,
        `R|${c.region.get(id)!}|p:${parentColor}|c:${children.join(',')}|n:${nodes.join(',')}`])
    }
    for (const id of idx.nodeIds) {
      const identityWires = idx.identityIncidentWires.get(id)
      const ports = identityWires === undefined
        ? idx.nodePortOrder.get(id)!.map((pk) => {
            const wireId = idx.nodePortWire.get(id)!.get(pk)
            if (wireId === undefined) {
              throw new DiagramError(`port '${pk}' missing wire for node '${id}'`)
            }
            return `${pk}=${c.wire.get(wireId)!}`
          })
        : identityWires
            .map((wireId) => c.wire.get(wireId)!)
            .sort((left, right) => left - right)
            .map((color) => `i=${color}`)
      entries.push([`${side}|N${id}`,
        `N|${c.node.get(id)!}|r:${c.region.get(idx.nodeRegion.get(id)!)!}|${ports.join(',')}`])
    }
    for (const id of idx.wireIds) {
      const eps = idx.wireEndpoints.get(id)!.map((ep) => `${c.node.get(ep.node)!}.${ep.pkey}`).sort()
      entries.push([`${side}|W${id}`,
        `W|${c.wire.get(id)!}|sig:${idx.wireSigKey.get(id)!}|e:${eps.join(',')}`])
    }
  })
  const ranked = rankSignatures(entries)
  return indexes.map((idx, side) => ({
    region: new Map(idx.regionIds.map((id) => [id, ranked.get(`${side}|R${id}`)!])),
    node: new Map(idx.nodeIds.map((id) => [id, ranked.get(`${side}|N${id}`)!])),
    wire: new Map(idx.wireIds.map((id) => [id, ranked.get(`${side}|W${id}`)!])),
  }))
}

function refine(indexes: readonly RefineIndex[], c0: readonly MutableColors[]): MutableColors[] {
  let c = c0
  let classes = classCount(c)
  for (;;) {
    const next = refineOnce(indexes, c)
    const nextClasses = classCount(next)
    if (nextClasses === classes) return next
    c = next
    classes = nextClasses
  }
}

/** Every side's `RefineIndex`, built once and reused across every
 *  `refineJointlyIndexed` call over the same sides — indexes are pure in
 *  (diagram, pins), so a caller re-refining under many different `marks`
 *  (individualization search) never needs to rebuild them per attempt. */
export function buildRefineIndexes(sides: readonly RefinementSide[]): RefineIndex[] {
  return sides.map((s) => buildRefineIndex(s.diagram, s.pins))
}

/** The joint refinement core: colors `indexes` (already built) under `marks`. */
export function refineJointlyIndexed(
  indexes: readonly RefineIndex[],
  marks: readonly Mark[] = [],
): SideColors[] {
  return refine(indexes, initialColors(indexes, marks))
}

/**
 * Rank every side jointly to a stable-partition fixpoint: colors seed from
 * content-only signature strings (shared vocabulary across sides, so equal
 * colors on different sides mean corresponding structure), folding each
 * `Mark`'s token into its element's initial signature (`|#token`) so paired
 * marks — and only paired marks — start in their own class; refinement then
 * repeatedly re-derives every element's signature from its current
 * neighborhood colors until the joint class count stops growing. Marks are
 * strictly class-splitting: they only ever divide an initial class, never
 * merge two elements that content alone kept apart. Builds each side's
 * `RefineIndex` fresh — callers re-refining the same sides under many
 * different `marks` should call `buildRefineIndexes` once and use
 * `refineJointlyIndexed` instead.
 */
export function refineJointly(
  sides: readonly RefinementSide[],
  marks: readonly Mark[] = [],
): SideColors[] {
  return refineJointlyIndexed(buildRefineIndexes(sides), marks)
}
