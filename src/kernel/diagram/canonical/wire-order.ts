import type { Diagram, WireId } from '../diagram'
import { buildRefineIndex, refineJointly, type Mark, type RefineIndex, type SideColors } from './refine'

/**
 * Discrete canonical wire ordinals — the definition-argument order.
 * Individualization-refinement with lex-min serialization: a class
 * refinement cannot split is an automorphism orbit ONLY when every member
 * is explored, so this search tries each and keeps the least form. Cold
 * path (once per definition, small bodies) — no orbit pruning by design.
 *
 * Contract: deterministic (a pure function of the diagram) and id-invariant
 * — isomorphic diagrams receive corresponding wire ordinals, so isomorphic
 * selections get the same argument order. When a genuine automorphism orbit
 * ties several wires together, this search's own lex-min winner picks among
 * the tied total orders; nothing requires that winner to coincide with any
 * other canonicalization engine's choice among the same tied orders.
 */
export function canonicalWireOrder(d: Diagram): Map<WireId, number> {
  const idx = buildRefineIndex(d, [])
  const best = search([])
  return ordinalize(idx.wireIds, best.colors.wire)

  function search(marks: readonly Mark[]): { form: string; colors: SideColors } {
    const [colors] = refineJointly([{ diagram: d, pins: [] }], marks)
    const tied = firstTiedClass(colors!)
    if (tied === null) return { form: serialize(idx, colors!), colors: colors! }
    let best: { form: string; colors: SideColors } | null = null
    for (const member of tied.members) {
      const s = search([...marks, { side: 0, sort: tied.sort, id: member, token: marks.length }])
      if (best === null || s.form < best.form) best = s
    }
    return best!
  }
}

/** First tied class: members sharing the smallest tied color, in a fixed sort order. */
function firstTiedClass(c: SideColors): { sort: 'region' | 'node' | 'wire'; members: string[] } | null {
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

function serialize(idx: RefineIndex, c: SideColors): string {
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
    lines.push(`n${nodeOrd.get(id)!}:${idx.nodeContentKey.get(id)!}:r=r${regionOrd.get(idx.nodeRegion.get(id)!)!}`)
  }
  for (const id of sortByOrd(idx.wireIds, wireOrd)) {
    const pins = idx.pinOf.get(id)
    const eps = idx.wireEndpoints.get(id)!.map((ep) => `n${nodeOrd.get(ep.node)!}.${ep.pkey}`).sort()
    const pinStr = pins === undefined ? '' : `pins${JSON.stringify(pins)}:`
    lines.push(`w${wireOrd.get(id)!}:${pinStr}sig=${idx.wireSigKey.get(id)!}:e=${eps.join(',')}`)
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
