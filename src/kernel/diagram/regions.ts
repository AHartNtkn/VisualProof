import type { Diagram, RegionId, WireId } from './diagram'
import { DiagramError } from './diagram'

function regionOf(d: Diagram, id: RegionId) {
  const r = d.regions[id]
  if (r === undefined) throw new DiagramError(`unknown region '${id}'`)
  return r
}

/** True iff anc lies on the parent chain of desc (inclusive). */
export function isAncestorOrEqual(d: Diagram, anc: RegionId, desc: RegionId): boolean {
  regionOf(d, anc)
  regionOf(d, desc) // the loop would also catch it; explicit for symmetry and intent
  let cur = desc
  for (;;) {
    const r = regionOf(d, cur)
    if (cur === anc) return true
    if (r.kind === 'sheet') return false
    cur = r.parent
  }
}

/** The deepest region lying on both parent chains (inclusive). */
export function deepestCommonAncestor(d: Diagram, a: RegionId, b: RegionId): RegionId {
  const chain = new Set<RegionId>()
  for (let cur = a; ; ) {
    chain.add(cur)
    const r = regionOf(d, cur)
    if (r.kind === 'sheet') break
    cur = r.parent
  }
  for (let cur = b; ; ) {
    if (chain.has(cur)) return cur
    const r = regionOf(d, cur)
    if (r.kind === 'sheet') throw new DiagramError(`regions '${a}' and '${b}' share no ancestor`)
    cur = r.parent
  }
}

/** Number of cuts on the path from the root to r, counting r itself if it is a cut. */
export function cutDepth(d: Diagram, id: RegionId): number {
  let depth = 0
  let cur = id
  for (;;) {
    const r = regionOf(d, cur)
    if (r.kind === 'cut') depth++
    if (r.kind === 'sheet') return depth
    cur = r.parent
  }
}

/** Positive iff the cut depth is even (spec §2.1). */
export function polarity(d: Diagram, id: RegionId): 'positive' | 'negative' {
  return cutDepth(d, id) % 2 === 0 ? 'positive' : 'negative'
}

/**
 * The derived scope of one wire: the deepest common ancestor of its
 * incidence regions — endpoint node regions, plus the root once if the wire
 * appears on the boundary. This is where the wire's quantifier reads
 * (derived-scope identity rules spec §1). Total on every validated diagram:
 * the two-end floor guarantees at least one incidence.
 */
export function derivedScope(
  d: Diagram,
  wireId: WireId,
  boundary: readonly WireId[] = [],
): RegionId {
  const wire = d.wires[wireId]
  if (wire === undefined) throw new DiagramError(`unknown wire '${wireId}'`)
  let dca: RegionId | null = boundary.includes(wireId) ? d.root : null
  for (const endpoint of wire.endpoints) {
    const node = d.nodes[endpoint.node]
    if (node === undefined) {
      throw new DiagramError(`wire '${wireId}' endpoint references missing node '${endpoint.node}'`)
    }
    dca = dca === null ? node.region : deepestCommonAncestor(d, dca, node.region)
  }
  if (dca === null) {
    throw new DiagramError(`wire '${wireId}' has no incidences; its scope is undefined`)
  }
  return dca
}

/** Derived scopes of every wire at once (one pass over the endpoints). */
export function derivedScopes(
  d: Diagram,
  boundary: readonly WireId[] = [],
): Map<WireId, RegionId> {
  const out = new Map<WireId, RegionId>()
  for (const wireId of Object.keys(d.wires)) {
    out.set(wireId, derivedScope(d, wireId, boundary))
  }
  return out
}

/** True iff the wire's derived scope encloses `region` — the visibility test. */
export function wireVisibleAt(
  d: Diagram,
  wireId: WireId,
  region: RegionId,
  boundary: readonly WireId[] = [],
): boolean {
  return isAncestorOrEqual(d, derivedScope(d, wireId, boundary), region)
}
