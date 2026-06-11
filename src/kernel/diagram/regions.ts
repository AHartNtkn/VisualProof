import type { Diagram, RegionId } from './diagram'
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

/**
 * Positive iff the cut depth is even. Bubbles are quantifiers, not negations:
 * they never affect parity (spec §2.1).
 */
export function polarity(d: Diagram, id: RegionId): 'positive' | 'negative' {
  return cutDepth(d, id) % 2 === 0 ? 'positive' : 'negative'
}
