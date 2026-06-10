import type { Diagram, NodeId, RegionId, WireId } from '../diagram'
import { DiagramError } from '../diagram'
import { canonicalLabeling } from './canonical'

export type DiagramIso = {
  readonly regions: ReadonlyMap<RegionId, RegionId>
  readonly nodes: ReadonlyMap<NodeId, NodeId>
  readonly wires: ReadonlyMap<WireId, WireId>
}

/**
 * An isomorphism from `from` onto `to`, or null when none exists. Built by
 * matching canonical-labeling ordinals: equal forms mean the discrete
 * colorings correspond, and the ordinal-matched mapping transports all
 * structure (the canonical serialization writes every reference by ordinal).
 * For diagrams with automorphisms this picks one of the valid isomorphisms,
 * deterministically.
 */
export function isoBetween(from: Diagram, to: Diagram): DiagramIso | null {
  const a = canonicalLabeling(from)
  const b = canonicalLabeling(to)
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
