import type { Diagram, DiagramNode, NodeId, RegionId, WireId } from '../diagram'
import { DiagramError } from '../diagram'
import { freePorts } from '../../term/term'
import { termShapeKey, positionalPortKey } from './shape'

export type CanonicalLabeling = {
  readonly form: string
  readonly regionOrd: ReadonlyMap<RegionId, number>
  readonly nodeOrd: ReadonlyMap<NodeId, number>
  readonly wireOrd: ReadonlyMap<WireId, number>
}

/**
 * Exact canonical form by individualization-refinement.
 *
 * Colors: every region, node, and wire carries an integer color. Initial
 * colors come from isomorphism-invariant local content (kind, arity, shape
 * key, boundary pin). Refinement rounds replace each object's color with the
 * rank of its signature — old color plus the colors of its neighborhood —
 * until the number of color classes stabilizes. Old colors prefix every
 * signature, so refinement only ever splits classes, never merges: the class
 * count is monotone and the loop terminates.
 *
 * If classes remain tied (genuine symmetry), pick the first tied class
 * (smallest color) and branch: individualize each member in turn, re-refine,
 * recurse, and keep the lexicographically smallest serialization. Every
 * member of the tied class is explored, so the minimum is invariant under
 * isomorphism — this is what makes the form exact rather than heuristic.
 * Worst case exponential; proof diagrams are small.
 *
 * Pinned wires (the boundary of a DiagramWithBoundary) get distinct initial
 * colors in pin order, so boundary order is significant.
 */
export function canonicalForm(d: Diagram, pinnedWires: readonly WireId[] = []): string {
  return canonicalLabeling(d, pinnedWires).form
}

/**
 * The canonical form together with the winning discrete coloring's ordinals.
 * Corresponding objects of isomorphic diagrams receive equal ordinals — the
 * basis for isomorphism extraction (iso.ts) and proof composition (proof/compose.ts).
 */
export function canonicalLabeling(d: Diagram, pinnedWires: readonly WireId[] = []): CanonicalLabeling {
  const seenPins = new Set<string>()
  for (const w of pinnedWires) {
    if (d.wires[w] === undefined) throw new DiagramError(`pinned wire '${w}' does not exist`)
    if (seenPins.has(w)) throw new DiagramError(`duplicate pinned wire '${w}'`)
    seenPins.add(w)
  }
  const idx = buildIndex(d, pinnedWires)
  const { form, colors } = search(idx, refine(idx, initialColors(idx)))
  return {
    form,
    regionOrd: ordinalize(idx.regionIds, colors.region),
    nodeOrd: ordinalize(idx.nodeIds, colors.node),
    wireOrd: ordinalize(idx.wireIds, colors.wire),
  }
}

type Index = {
  readonly regionIds: readonly RegionId[]
  readonly nodeIds: readonly NodeId[]
  readonly wireIds: readonly WireId[]
  readonly regionKindKey: ReadonlyMap<RegionId, string>
  readonly parentOf: ReadonlyMap<RegionId, RegionId | null>
  readonly childrenOf: ReadonlyMap<RegionId, readonly RegionId[]>
  readonly nodesIn: ReadonlyMap<RegionId, readonly NodeId[]>
  readonly wiresScoped: ReadonlyMap<RegionId, readonly WireId[]>
  readonly nodeContentKey: ReadonlyMap<NodeId, string>
  readonly nodeRegion: ReadonlyMap<NodeId, RegionId>
  readonly nodeBinder: ReadonlyMap<NodeId, RegionId | null>
  readonly nodePortOrder: ReadonlyMap<NodeId, readonly string[]>
  readonly nodePortWire: ReadonlyMap<NodeId, ReadonlyMap<string, WireId>>
  readonly wireScope: ReadonlyMap<WireId, RegionId>
  readonly wireEndpoints: ReadonlyMap<WireId, readonly { node: NodeId; pkey: string }[]>
  readonly pinOf: ReadonlyMap<WireId, number>
}

function buildIndex(d: Diagram, pinned: readonly WireId[]): Index {
  const regionIds = Object.keys(d.regions)
  const nodeIds = Object.keys(d.nodes)
  const wireIds = Object.keys(d.wires)

  const regionKindKey = new Map<RegionId, string>()
  const parentOf = new Map<RegionId, RegionId | null>()
  const childrenOf = new Map<RegionId, RegionId[]>()
  const nodesIn = new Map<RegionId, NodeId[]>()
  const wiresScoped = new Map<RegionId, WireId[]>()
  for (const id of regionIds) {
    childrenOf.set(id, [])
    nodesIn.set(id, [])
    wiresScoped.set(id, [])
  }
  for (const id of regionIds) {
    const r = d.regions[id]!
    regionKindKey.set(id, r.kind === 'bubble' ? `bubble/${r.arity}` : r.kind)
    if (r.kind === 'sheet') {
      parentOf.set(id, null)
    } else {
      parentOf.set(id, r.parent)
      childrenOf.get(r.parent)!.push(id)
    }
  }

  const nodeContentKey = new Map<NodeId, string>()
  const nodeRegion = new Map<NodeId, RegionId>()
  const nodeBinder = new Map<NodeId, RegionId | null>()
  const nodePortOrder = new Map<NodeId, string[]>()
  const nodePortWire = new Map<NodeId, Map<string, WireId>>()
  // Return-typed switch (no default): a new node kind forces its canonical
  // content key, binder, and port order to be decided here.
  const nodeCanon = (id: NodeId, n: DiagramNode): { contentKey: string; binder: RegionId | null; portOrder: string[] } => {
    switch (n.kind) {
      case 'term':
        return {
          contentKey: `term:${termShapeKey(n.term)}`,
          binder: null,
          // positional v-keys: one per free port, already in first-occurrence order
          portOrder: ['out', ...freePorts(n.term).map((_, i) => `v${i}`)],
        }
      case 'atom': {
        const binder = d.regions[n.binder]!
        if (binder.kind !== 'bubble') {
          // Unreachable for mkDiagram-validated diagrams; throw rather than fabricate.
          throw new DiagramError(`atom '${id}' binder '${n.binder}' is not a bubble`)
        }
        return {
          contentKey: 'atom',
          binder: n.binder,
          portOrder: Array.from({ length: binder.arity }, (_, i) => `a${i}`),
        }
      }
    }
  }
  for (const id of nodeIds) {
    const n = d.nodes[id]!
    nodeRegion.set(id, n.region)
    nodesIn.get(n.region)!.push(id)
    nodePortWire.set(id, new Map())
    const canon = nodeCanon(id, n)
    nodeContentKey.set(id, canon.contentKey)
    nodeBinder.set(id, canon.binder)
    nodePortOrder.set(id, canon.portOrder)
  }

  const wireScope = new Map<WireId, RegionId>()
  const wireEndpoints = new Map<WireId, { node: NodeId; pkey: string }[]>()
  for (const id of wireIds) {
    const w = d.wires[id]!
    wireScope.set(id, w.scope)
    wiresScoped.get(w.scope)!.push(id)
    const eps = w.endpoints.map((ep) => {
      const n = d.nodes[ep.node]!
      // Return-typed switch (no default): a new node kind forces its positional
      // port key to be decided here.
      const pkey: string = ((): string => {
        switch (n.kind) {
          case 'term':
            return positionalPortKey(n.term, ep.port)
          case 'atom':
            if (ep.port.kind === 'arg') return `a${ep.port.index}`
            // mkDiagram's port-membership check makes this unreachable: atoms have
            // only arg ports. Throw rather than fabricate.
            throw new DiagramError(`atom '${ep.node}' cannot carry port '${ep.port.kind}'`)
        }
      })()
      nodePortWire.get(ep.node)!.set(pkey, id)
      return { node: ep.node, pkey }
    })
    wireEndpoints.set(id, eps)
  }

  const pinOf = new Map<WireId, number>()
  pinned.forEach((w, i) => pinOf.set(w, i))

  return {
    regionIds, nodeIds, wireIds, regionKindKey, parentOf, childrenOf, nodesIn,
    wiresScoped, nodeContentKey, nodeRegion, nodeBinder, nodePortOrder,
    nodePortWire, wireScope, wireEndpoints, pinOf,
  }
}

type Colors = {
  readonly region: ReadonlyMap<RegionId, number>
  readonly node: ReadonlyMap<NodeId, number>
  readonly wire: ReadonlyMap<WireId, number>
}

function classCount(c: Colors): number {
  return new Set([...c.region.values(), ...c.node.values(), ...c.wire.values()]).size
}

function rankSignatures(entries: [string, string][]): Map<string, number> {
  const distinct = [...new Set(entries.map(([, sig]) => sig))].sort()
  const rank = new Map(distinct.map((s, i) => [s, i]))
  const out = new Map<string, number>()
  for (const [id, sig] of entries) out.set(id, rank.get(sig)!)
  return out
}

function initialColors(idx: Index): Colors {
  const entries: [string, string][] = []
  for (const id of idx.regionIds) entries.push([`R${id}`, `R|${idx.regionKindKey.get(id)!}`])
  for (const id of idx.nodeIds) entries.push([`N${id}`, `N|${idx.nodeContentKey.get(id)!}`])
  for (const id of idx.wireIds) {
    const pin = idx.pinOf.get(id)
    entries.push([`W${id}`, `W|${pin === undefined ? 'w' : `pin${pin}`}`])
  }
  const ranked = rankSignatures(entries)
  return {
    region: new Map(idx.regionIds.map((id) => [id, ranked.get(`R${id}`)!])),
    node: new Map(idx.nodeIds.map((id) => [id, ranked.get(`N${id}`)!])),
    wire: new Map(idx.wireIds.map((id) => [id, ranked.get(`W${id}`)!])),
  }
}

function refineOnce(idx: Index, c: Colors): Colors {
  const entries: [string, string][] = []
  for (const id of idx.regionIds) {
    const parent = idx.parentOf.get(id)
    const children = idx.childrenOf.get(id)!.map((x) => {
      const col = c.region.get(x)
      if (col === undefined) throw new DiagramError(`child region '${x}' missing color`)
      return col
    }).sort((a, b) => a - b)
    const nodes = idx.nodesIn.get(id)!.map((x) => {
      const col = c.node.get(x)
      if (col === undefined) throw new DiagramError(`node '${x}' missing color`)
      return col
    }).sort((a, b) => a - b)
    const wires = idx.wiresScoped.get(id)!.map((x) => {
      const col = c.wire.get(x)
      if (col === undefined) throw new DiagramError(`wire '${x}' missing color`)
      return col
    }).sort((a, b) => a - b)
    const parentColor = parent === null ? '-' : (() => {
      const col = c.region.get(parent as RegionId)
      if (col === undefined) throw new DiagramError(`parent region '${parent}' missing color`)
      return String(col)
    })()
    const regionColor = c.region.get(id)
    if (regionColor === undefined) throw new DiagramError(`region '${id}' missing color`)
    entries.push([`R${id}`,
      `R|${regionColor}|p:${parentColor}|c:${children.join(',')}|n:${nodes.join(',')}|w:${wires.join(',')}`])
  }
  // Lookups here use `!`: totality follows from buildIndex construction and
  // mkDiagram's port-partition invariant (see docs/kernel/canonicalization.md).
  for (const id of idx.nodeIds) {
    const binder = idx.nodeBinder.get(id)
    const ports = idx.nodePortOrder.get(id)!
      .map((pk) => {
        const wireId = idx.nodePortWire.get(id)!.get(pk)
        if (wireId === undefined) throw new DiagramError(`port '${pk}' missing wire for node '${id}'`)
        const wireColor = c.wire.get(wireId)
        if (wireColor === undefined) throw new DiagramError(`wire '${wireId}' missing color`)
        return `${pk}=${wireColor}`
      })
    entries.push([`N${id}`,
      `N|${c.node.get(id)!}|r:${c.region.get(idx.nodeRegion.get(id)!)!}|b:${binder == null ? '-' : c.region.get(binder)!}|${ports.join(',')}`])
  }
  for (const id of idx.wireIds) {
    const eps = idx.wireEndpoints.get(id)!
      .map((ep) => `${c.node.get(ep.node)!}.${ep.pkey}`)
      .sort()
    entries.push([`W${id}`,
      `W|${c.wire.get(id)!}|s:${c.region.get(idx.wireScope.get(id)!)!}|e:${eps.join(',')}`])
  }
  const ranked = rankSignatures(entries)
  return {
    region: new Map(idx.regionIds.map((id) => [id, ranked.get(`R${id}`)!])),
    node: new Map(idx.nodeIds.map((id) => [id, ranked.get(`N${id}`)!])),
    wire: new Map(idx.wireIds.map((id) => [id, ranked.get(`W${id}`)!])),
  }
}

function refine(idx: Index, c0: Colors): Colors {
  let c = c0
  let classes = classCount(c)
  for (;;) {
    const next = refineOnce(idx, c)
    const nextClasses = classCount(next)
    if (nextClasses === classes) return next
    c = next
    classes = nextClasses
  }
}

/** First tied class: members sharing the smallest tied color, in a fixed sort order. */
function firstTiedClass(c: Colors): { sort: 'region' | 'node' | 'wire'; members: string[] } | null {
  let bestColor = Infinity
  let bestSort: 'region' | 'node' | 'wire' = 'region'
  let bestMembers: string[] = []
  let found = false

  const consider = (sort: 'region' | 'node' | 'wire', m: ReadonlyMap<string, number>) => {
    const byColor = new Map<number, string[]>()
    for (const [id, col] of m) {
      const arr = byColor.get(col)
      if (arr === undefined) byColor.set(col, [id])
      else arr.push(id)
    }
    for (const [col, members] of byColor) {
      if (members.length > 1 && col < bestColor) {
        bestColor = col
        bestSort = sort
        bestMembers = members.sort()
        found = true
      }
    }
  }

  // colors are globally ranked across sorts, so comparing color values across
  // sorts is well-defined; sort identity rides along for map selection only
  consider('region', c.region)
  consider('node', c.node)
  consider('wire', c.wire)
  return found ? { sort: bestSort, members: bestMembers } : null
}

function individualize(c: Colors, sort: 'region' | 'node' | 'wire', id: string): Colors {
  const bump = classCount(c)
  const clone: { region: Map<string, number>; node: Map<string, number>; wire: Map<string, number> } = {
    region: new Map(c.region),
    node: new Map(c.node),
    wire: new Map(c.wire),
  }
  clone[sort].set(id, bump)
  return clone
}

function search(idx: Index, c: Colors): { form: string; colors: Colors } {
  const tied = firstTiedClass(c)
  if (tied === null) return { form: serializeWith(idx, c), colors: c }
  let best: { form: string; colors: Colors } | null = null
  for (const member of tied.members) {
    const s = search(idx, refine(idx, individualize(c, tied.sort, member)))
    if (best === null || s.form < best.form) best = s
  }
  return best!
}

function serializeWith(idx: Index, c: Colors): string {
  const regionOrd = ordinalize(idx.regionIds, c.region)
  const nodeOrd = ordinalize(idx.nodeIds, c.node)
  const wireOrd = ordinalize(idx.wireIds, c.wire)
  const lines: string[] = []
  for (const id of sortByOrd(idx.regionIds, regionOrd)) {
    const parent = idx.parentOf.get(id)
    const parentStr = parent === null ? '-' : (() => {
      const ord = regionOrd.get(parent as RegionId)
      if (ord === undefined) throw new DiagramError(`parent region '${parent}' missing ordinal`)
      return `r${ord}`
    })()
    const regionOrdinal = regionOrd.get(id)
    if (regionOrdinal === undefined) throw new DiagramError(`region '${id}' missing ordinal`)
    lines.push(`r${regionOrdinal}:${idx.regionKindKey.get(id)!}:p=${parentStr}`)
  }
  for (const id of sortByOrd(idx.nodeIds, nodeOrd)) {
    const binder = idx.nodeBinder.get(id)
    const nodeOrdinal = nodeOrd.get(id)
    if (nodeOrdinal === undefined) throw new DiagramError(`node '${id}' missing ordinal`)
    const regionId = idx.nodeRegion.get(id)
    if (regionId === undefined) throw new DiagramError(`node '${id}' missing region`)
    const regionOrdinal = regionOrd.get(regionId)
    if (regionOrdinal === undefined) throw new DiagramError(`region '${regionId}' missing ordinal`)
    const binderStr = binder === null ? '' : (() => {
      const binderOrdinal = regionOrd.get(binder as RegionId)
      if (binderOrdinal === undefined) throw new DiagramError(`binder region '${binder}' missing ordinal`)
      return `:b=r${binderOrdinal}`
    })()
    lines.push(`n${nodeOrdinal}:${idx.nodeContentKey.get(id)!}:r=r${regionOrdinal}${binderStr}`)
  }
  for (const id of sortByOrd(idx.wireIds, wireOrd)) {
    const pin = idx.pinOf.get(id)
    const eps = idx.wireEndpoints.get(id)!
      .map((ep) => {
        const nodeOrdinal = nodeOrd.get(ep.node)
        if (nodeOrdinal === undefined) throw new DiagramError(`node '${ep.node}' missing ordinal`)
        return `n${nodeOrdinal}.${ep.pkey}`
      })
      .sort()
    const wireOrdinal = wireOrd.get(id)
    if (wireOrdinal === undefined) throw new DiagramError(`wire '${id}' missing ordinal`)
    const scopeId = idx.wireScope.get(id)
    if (scopeId === undefined) throw new DiagramError(`wire '${id}' missing scope`)
    const scopeOrdinal = regionOrd.get(scopeId)
    if (scopeOrdinal === undefined) throw new DiagramError(`scope region '${scopeId}' missing ordinal`)
    const pinStr = pin === undefined ? '' : `pin${pin}:`
    lines.push(`w${wireOrdinal}:${pinStr}s=r${scopeOrdinal}:e=${eps.join(',')}`)
  }
  return lines.join('\n')
}

function ordinalize(ids: readonly string[], colors: ReadonlyMap<string, number>): Map<string, number> {
  const sorted = [...ids].sort((a, b) => colors.get(a)! - colors.get(b)!)
  return new Map(sorted.map((id, i) => [id, i]))
}

function sortByOrd(ids: readonly string[], ord: ReadonlyMap<string, number>): string[] {
  return [...ids].sort((a, b) => ord.get(a)! - ord.get(b)!)
}
