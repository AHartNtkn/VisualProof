import type { Diagram, DiagramNode, NodeId, Port, RegionId, WireId } from '../diagram'
import { DiagramError } from '../diagram'
import type { DiagramWithBoundary } from '../boundary'
import { freePorts } from '../../term/term'
import { termShapeKey, positionalPortKey } from './shape'

/**
 * THE CANONICAL EXPLORER (labeling mode).
 *
 * A diagram is a port-hypergraph: nodes carry ORDERED positional ports, so
 * exploration from an anchor is deterministic wherever ports decide the next
 * step. The two sources of genuine unorderedness are equality wires (their
 * endpoints have no order) and sibling regions (a region's children are a
 * set). The explorer assigns every region/node/wire a canonical ordinal such
 * that isomorphic diagrams receive corresponding ordinals.
 *
 * Mechanically the exploration is individualization-refinement seeded by the
 * anchor: each pinned boundary wire gets the ordered vector of positions at
 * which it occurs (their order and aliasing are the open-diagram anchor);
 * every object otherwise starts colored by its
 * isomorphism-invariant local content (kind, arity, exact term shape). A
 * refinement round replaces each color by the rank of its neighborhood
 * signature — the ordered-port keys make a node's signature order-sensitive,
 * while unordered wire-endpoint and sibling-region sets enter as SORTED color
 * multisets (this is the "defer the set" step: a set whose members are already
 * distinguished elsewhere is split with no choice). Rounds only ever split
 * classes, so the class count is monotone and refinement terminates.
 *
 * A class refinement cannot split is a genuine automorphism orbit. Only then
 * is a choice forced: individualize each member in turn, re-refine, recurse,
 * and keep the lexicographically least serialization. Every member is
 * explored, so the minimum is invariant — this is what makes the labeling a
 * COMPLETE invariant (equal forms iff isomorphic) rather than a heuristic.
 *
 * TERM COMPARISON IS EXACT (USER RULING): free ports name-blind by positional
 * role, but bodies compared by structural de Bruijn identity — never modulo
 * beta-eta. The labeling is therefore total, deterministic, and fuel-free.
 * Beta-eta looseness lives only in the matcher's node-compatibility, never in
 * this invariant.
 */

export type ExploreLabeling = {
  readonly form: string
  readonly regionOrd: ReadonlyMap<RegionId, number>
  readonly nodeOrd: ReadonlyMap<NodeId, number>
  readonly wireOrd: ReadonlyMap<WireId, number>
}

/** The canonical serialization: equal strings iff isomorphic diagrams. */
export function exploreForm(d: Diagram, pinnedWires: readonly WireId[] = []): string {
  return exploreLabeling(d, pinnedWires).form
}

/**
 * Canonical form of a bounded diagram: the diagram pinned by its boundary
 * order. Equal strings iff the two bounded diagrams are isomorphic respecting
 * boundary order — the exactness guarantee relFold, comprehension abstraction,
 * and theorem citation rely on. With an empty boundary this equals
 * `exploreForm` of the diagram (a 0-ary relation is a sentence).
 */
export function boundaryForm(dwb: DiagramWithBoundary): string {
  return exploreForm(dwb.diagram, dwb.boundary)
}

/**
 * The canonical form together with the winning discrete coloring's ordinals.
 * Corresponding objects of isomorphic diagrams receive equal ordinals — the
 * basis for isomorphism extraction and proof composition.
 */
export function exploreLabeling(d: Diagram, pinnedWires: readonly WireId[] = []): ExploreLabeling {
  for (const w of pinnedWires) {
    if (d.wires[w] === undefined) throw new DiagramError(`pinned wire '${w}' does not exist`)
  }
  const idx = buildExploreIndex(d, pinnedWires)
  const { form, colors } = search(idx, refine(idx, initialColors(idx)))
  return {
    form,
    regionOrd: ordinalize(idx.regionIds, colors.region),
    nodeOrd: ordinalize(idx.nodeIds, colors.node),
    wireOrd: ordinalize(idx.wireIds, colors.wire),
  }
}

export type RefinedColors = {
  readonly region: ReadonlyMap<RegionId, number>
  readonly node: ReadonlyMap<NodeId, number>
  readonly wire: ReadonlyMap<WireId, number>
}

/**
 * The refinement fixpoint colors (BEFORE any individualization). Two objects
 * with the same color are indistinguishable by the exploration — a sound
 * over-approximation of automorphism orbits (orbits refine colors; colors are
 * never finer than orbits). The matcher uses this to break the symmetry of
 * interchangeable pattern items: same-color siblings are forced onto host
 * candidates in increasing order, collapsing their factorial of equivalent
 * assignments to the one canonical representative.
 */
export function refinedColors(d: Diagram, pinnedWires: readonly WireId[] = []): RefinedColors {
  for (const w of pinnedWires) {
    if (d.wires[w] === undefined) throw new DiagramError(`pinned wire '${w}' does not exist`)
  }
  const idx = buildExploreIndex(d, pinnedWires)
  const c = refine(idx, initialColors(idx))
  return { region: c.region, node: c.node, wire: c.wire }
}

export type ExploreIndex = {
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
  /** Every ordered boundary position exposing this wire. */
  readonly pinOf: ReadonlyMap<WireId, readonly number[]>
}

/** Positional port key of a wire endpoint (name-blind). */
function endpointKey(d: Diagram, node: NodeId, port: Port): string {
  const n = d.nodes[node]!
  // Return-typed switch (no default): a new node kind must decide its key here.
  switch (n.kind) {
    case 'term':
      return positionalPortKey(n.term, port)
    case 'atom':
      if (port.kind === 'arg') return `a${port.index}`
      throw new DiagramError(`atom '${node}' cannot carry port '${port.kind}'`)
    case 'ref':
      if (port.kind === 'arg') return `a${port.index}`
      throw new DiagramError(`ref '${node}' cannot carry port '${port.kind}'`)
  }
}

export function buildExploreIndex(d: Diagram, pinned: readonly WireId[]): ExploreIndex {
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
          portOrder: ['out', ...freePorts(n.term).map((_, i) => `v${i}`)],
        }
      case 'atom': {
        const binder = d.regions[n.binder]!
        if (binder.kind !== 'bubble') {
          throw new DiagramError(`atom '${id}' binder '${n.binder}' is not a bubble`)
        }
        return {
          contentKey: 'atom',
          binder: n.binder,
          portOrder: Array.from({ length: binder.arity }, (_, i) => `a${i}`),
        }
      }
      case 'ref':
        return {
          contentKey: `ref:${n.defId}:${n.arity}`,
          binder: null,
          portOrder: Array.from({ length: n.arity }, (_, i) => `a${i}`),
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
      const pkey = endpointKey(d, ep.node, ep.port)
      nodePortWire.get(ep.node)!.set(pkey, id)
      return { node: ep.node, pkey }
    })
    wireEndpoints.set(id, eps)
  }

  const pinOf = new Map<WireId, number[]>()
  pinned.forEach((w, i) => {
    const positions = pinOf.get(w)
    if (positions === undefined) pinOf.set(w, [i])
    else positions.push(i)
  })

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

function initialColors(idx: ExploreIndex): Colors {
  const entries: [string, string][] = []
  for (const id of idx.regionIds) entries.push([`R${id}`, `R|${idx.regionKindKey.get(id)!}`])
  for (const id of idx.nodeIds) entries.push([`N${id}`, `N|${idx.nodeContentKey.get(id)!}`])
  for (const id of idx.wireIds) {
    const pins = idx.pinOf.get(id)
    entries.push([`W${id}`, `W|${pins === undefined ? 'w' : `pins${JSON.stringify(pins)}`}`])
  }
  const ranked = rankSignatures(entries)
  return {
    region: new Map(idx.regionIds.map((id) => [id, ranked.get(`R${id}`)!])),
    node: new Map(idx.nodeIds.map((id) => [id, ranked.get(`N${id}`)!])),
    wire: new Map(idx.wireIds.map((id) => [id, ranked.get(`W${id}`)!])),
  }
}

function refineOnce(idx: ExploreIndex, c: Colors): Colors {
  const entries: [string, string][] = []
  for (const id of idx.regionIds) {
    const parent = idx.parentOf.get(id)
    const children = idx.childrenOf.get(id)!.map((x) => c.region.get(x)!).sort((a, b) => a - b)
    const nodes = idx.nodesIn.get(id)!.map((x) => c.node.get(x)!).sort((a, b) => a - b)
    const wires = idx.wiresScoped.get(id)!.map((x) => c.wire.get(x)!).sort((a, b) => a - b)
    const parentColor = parent == null ? '-' : String(c.region.get(parent)!)
    entries.push([`R${id}`,
      `R|${c.region.get(id)!}|p:${parentColor}|c:${children.join(',')}|n:${nodes.join(',')}|w:${wires.join(',')}`])
  }
  for (const id of idx.nodeIds) {
    const binder = idx.nodeBinder.get(id)
    const ports = idx.nodePortOrder.get(id)!.map((pk) => {
      const wireId = idx.nodePortWire.get(id)!.get(pk)
      if (wireId === undefined) throw new DiagramError(`port '${pk}' missing wire for node '${id}'`)
      return `${pk}=${c.wire.get(wireId)!}`
    })
    entries.push([`N${id}`,
      `N|${c.node.get(id)!}|r:${c.region.get(idx.nodeRegion.get(id)!)!}|b:${binder == null ? '-' : c.region.get(binder)!}|${ports.join(',')}`])
  }
  for (const id of idx.wireIds) {
    const eps = idx.wireEndpoints.get(id)!.map((ep) => `${c.node.get(ep.node)!}.${ep.pkey}`).sort()
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

function refine(idx: ExploreIndex, c0: Colors): Colors {
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

function search(idx: ExploreIndex, c: Colors): { form: string; colors: Colors } {
  const tied = firstTiedClass(c)
  if (tied === null) return { form: serializeWith(idx, c), colors: c }
  let best: { form: string; colors: Colors } | null = null
  for (const member of tied.members) {
    const s = search(idx, refine(idx, individualize(c, tied.sort, member)))
    if (best === null || s.form < best.form) best = s
  }
  return best!
}

function serializeWith(idx: ExploreIndex, c: Colors): string {
  const regionOrd = ordinalize(idx.regionIds, c.region)
  const nodeOrd = ordinalize(idx.nodeIds, c.node)
  const wireOrd = ordinalize(idx.wireIds, c.wire)
  const lines: string[] = []
  for (const id of sortByOrd(idx.regionIds, regionOrd)) {
    const parent = idx.parentOf.get(id)
    const parentStr = parent == null ? '-' : `r${regionOrd.get(parent)!}`
    lines.push(`r${regionOrd.get(id)!}:${idx.regionKindKey.get(id)!}:p=${parentStr}`)
  }
  for (const id of sortByOrd(idx.nodeIds, nodeOrd)) {
    const binder = idx.nodeBinder.get(id)
    const binderStr = binder == null ? '' : `:b=r${regionOrd.get(binder)!}`
    lines.push(`n${nodeOrd.get(id)!}:${idx.nodeContentKey.get(id)!}:r=r${regionOrd.get(idx.nodeRegion.get(id)!)!}${binderStr}`)
  }
  for (const id of sortByOrd(idx.wireIds, wireOrd)) {
    const pins = idx.pinOf.get(id)
    const eps = idx.wireEndpoints.get(id)!.map((ep) => `n${nodeOrd.get(ep.node)!}.${ep.pkey}`).sort()
    const pinStr = pins === undefined ? '' : `pins${JSON.stringify(pins)}:`
    lines.push(`w${wireOrd.get(id)!}:${pinStr}s=r${regionOrd.get(idx.wireScope.get(id)!)!}:e=${eps.join(',')}`)
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

export type DiagramIso = {
  readonly regions: ReadonlyMap<RegionId, RegionId>
  readonly nodes: ReadonlyMap<NodeId, NodeId>
  readonly wires: ReadonlyMap<WireId, WireId>
}

/**
 * An isomorphism from `from` onto `to`, or null when none exists. Built by
 * matching canonical-labeling ordinals: equal forms mean the discrete
 * colorings correspond, and the ordinal-matched mapping transports all
 * structure. For diagrams with automorphisms this picks one valid
 * isomorphism, deterministically.
 */
export function exploreIso(from: Diagram, to: Diagram): DiagramIso | null {
  const a = exploreLabeling(from)
  const b = exploreLabeling(to)
  if (a.form !== b.form) return null
  const invert = (m: ReadonlyMap<string, number>): Map<number, string> => {
    const r = new Map<number, string>()
    for (const [id, o] of m) r.set(o, id)
    return r
  }
  const make = (mA: ReadonlyMap<string, number>, mBInv: Map<number, string>): Map<string, string> => {
    const out = new Map<string, string>()
    for (const [id, o] of mA) {
      const img = mBInv.get(o)
      if (img === undefined) throw new DiagramError(`canonical labelings with equal forms disagree at ordinal ${o}`)
      out.set(id, img)
    }
    return out
  }
  return {
    regions: make(a.regionOrd, invert(b.regionOrd)),
    nodes: make(a.nodeOrd, invert(b.nodeOrd)),
    wires: make(a.wireOrd, invert(b.wireOrd)),
  }
}
