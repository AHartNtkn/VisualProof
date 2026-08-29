import type { Diagram, NodeId, RegionId, WireId } from '../diagram'
import { DiagramError, endpointPositionKey } from '../diagram'
import { sigEquals } from '../sig'
import { serializeTerm } from '../../term/serialize'
import { buildRefineIndexes, refineJointlyIndexed, type Mark, type Sort, type SideColors } from './refine'

/**
 * PAIRWISE ISOMORPHISM WITH VERIFIED WITNESS.
 *
 * Joint refinement colors two diagrams' regions/nodes/wires by content; equal
 * colors on both sides mean corresponding structure. Each side's `RefineIndex`
 * is built once (`buildRefineIndexes`) and reused across every individualized
 * recursion (`refineJointlyIndexed`), since only the color-seeding `marks`
 * change between attempts, never the diagrams. When refinement alone
 * leaves every class a singleton pair, the coloring already IS the bijection
 * — build it and verify it transports every piece of structure (a
 * `DiagramError` on verification failure is an engine bug, never "not
 * isomorphic", because a discrete census-matched coloring provably transports
 * structure).
 *
 * When a class stays tied (an automorphism orbit refinement cannot split —
 * see the six-ring/two-three-ring pair below), individualize one element of
 * the smallest tied class, paired across sides by a fresh token, and recurse
 * over every same-colored candidate on the other side. Colors are computed
 * from content only, so any true isomorphism must map the fixed element to
 * SOME member of its class on the other side, and every member is tried, so
 * the search is complete. Each recursion strictly grows the joint class
 * count (the marked pair becomes its own singleton class), so depth is
 * bounded by the total element count and the search terminates.
 */

export type DiagramIso = {
  readonly regions: ReadonlyMap<RegionId, RegionId>
  readonly nodes: ReadonlyMap<NodeId, NodeId>
  readonly wires: ReadonlyMap<WireId, WireId>
}

/** Production-neutral counters; tests assert backstop dormancy through them. */
export const __isoCounters = { individualizations: 0, failedCandidates: 0 }

export function sameDiagram(
  a: Diagram, b: Diagram,
  aPins: readonly WireId[] = [], bPins: readonly WireId[] = [],
): boolean {
  return diagramIso(a, b, aPins, bPins) !== null
}

type Group = { readonly sort: Sort; readonly color: number; readonly aMembers: string[]; readonly bMembers: string[] }

function buildGroups(ca: SideColors, cb: SideColors): Group[] {
  const bySort: { sort: Sort; a: ReadonlyMap<string, number>; b: ReadonlyMap<string, number> }[] = [
    { sort: 'region', a: ca.region, b: cb.region },
    { sort: 'node', a: ca.node, b: cb.node },
    { sort: 'wire', a: ca.wire, b: cb.wire },
  ]
  const groups = new Map<string, Group>()
  for (const { sort, a, b } of bySort) {
    for (const [id, color] of a) {
      const key = `${sort}|${color}`
      let g = groups.get(key)
      if (g === undefined) {
        g = { sort, color, aMembers: [], bMembers: [] }
        groups.set(key, g)
      }
      g.aMembers.push(id)
    }
    for (const [id, color] of b) {
      const key = `${sort}|${color}`
      let g = groups.get(key)
      if (g === undefined) {
        g = { sort, color, aMembers: [], bMembers: [] }
        groups.set(key, g)
      }
      g.bMembers.push(id)
    }
  }
  return [...groups.values()]
}

export function diagramIso(
  a: Diagram, b: Diagram,
  aPins: readonly WireId[] = [], bPins: readonly WireId[] = [],
): DiagramIso | null {
  if (aPins.length !== bPins.length) return null
  const indexes = buildRefineIndexes([{ diagram: a, pins: aPins }, { diagram: b, pins: bPins }])
  return attempt([])

  function attempt(marks: readonly Mark[]): DiagramIso | null {
    const [ca, cb] = refineJointlyIndexed(indexes, marks)
    const groups = buildGroups(ca!, cb!)

    for (const g of groups) {
      if (g.aMembers.length !== g.bMembers.length) return null
    }

    const tied = groups
      .filter((g) => g.aMembers.length > 1)
      .sort((x, y) => x.color - y.color)[0]

    if (tied === undefined) {
      const regions = new Map<RegionId, RegionId>()
      const nodes = new Map<NodeId, NodeId>()
      const wires = new Map<WireId, WireId>()
      for (const g of groups) {
        const aId = g.aMembers[0]!
        const bId = g.bMembers[0]!
        if (g.sort === 'region') regions.set(aId, bId)
        else if (g.sort === 'node') nodes.set(aId, bId)
        else wires.set(aId, bId)
      }
      const iso: DiagramIso = { regions, nodes, wires }
      const reason = __verifyIso(a, b, aPins, bPins, iso)
      if (reason !== null) {
        throw new DiagramError(`diagramIso: discrete census-matched witness failed verification: ${reason}`)
      }
      return iso
    }

    const aFixed = [...tied.aMembers].sort()[0]!
    const token = marks.length / 2
    for (const bCand of [...tied.bMembers].sort()) {
      __isoCounters.individualizations++
      const r = attempt([
        ...marks,
        { side: 0, sort: tied.sort, id: aFixed, token },
        { side: 1, sort: tied.sort, id: bCand, token },
      ])
      if (r !== null) return r
      __isoCounters.failedCandidates++
    }
    return null
  }
}

/**
 * Full bijection check: `map`'s key set must equal `domain` exactly and its
 * value set must equal `codomain` exactly (injective AND onto), as required
 * for a whole-diagram isomorphism where every element on both sides must
 * correspond. Injectivity is checked directly (a repeated image is rejected
 * on sight) rather than inferred from `image.size === codomain.size`, which
 * only detects collisions when `domain.size === codomain.size` — compare
 * `exactDomain` in `occurrence-certificate.ts`, which checks domain
 * completeness only (no codomain, no onto requirement), because an
 * occurrence certificate is an injective embedding of a pattern into a
 * generally larger host, not a bijection between two equal-sized sides.
 */
function checkBijection<K, V>(
  map: ReadonlyMap<K, V>, domain: ReadonlySet<K>, codomain: ReadonlySet<V>, label: string,
): string | null {
  if (map.size !== domain.size) return `${label} map has ${map.size} entries; expected ${domain.size}`
  const image = new Set<V>()
  for (const [k, v] of map) {
    if (!domain.has(k)) return `${label} map has unexpected key '${String(k)}'`
    if (!codomain.has(v)) return `${label} map targets unknown '${String(v)}'`
    if (image.has(v)) return `${label} map is not injective: '${String(v)}' has more than one preimage`
    image.add(v)
  }
  if (image.size !== codomain.size) return `${label} map is not onto its codomain`
  return null
}

/** Linear structural transport check; returns a reason or null. Exported
 *  under the file's `__`-prefixed test-seam convention (see `__isoCounters`)
 *  because every rejection branch here is unreachable through the public
 *  `diagramIso`/`sameDiagram` API on genuine engine inputs — see the module
 *  doc comment — and must be exercised by direct tests instead. */
export function __verifyIso(
  a: Diagram, b: Diagram,
  aPins: readonly WireId[], bPins: readonly WireId[],
  iso: DiagramIso,
): string | null {
  const aRegions = new Set(Object.keys(a.regions))
  const bRegions = new Set(Object.keys(b.regions))
  const aNodes = new Set(Object.keys(a.nodes))
  const bNodes = new Set(Object.keys(b.nodes))
  const aWires = new Set(Object.keys(a.wires))
  const bWires = new Set(Object.keys(b.wires))

  const regionsErr = checkBijection(iso.regions, aRegions, bRegions, 'regions')
  if (regionsErr !== null) return regionsErr
  const nodesErr = checkBijection(iso.nodes, aNodes, bNodes, 'nodes')
  if (nodesErr !== null) return nodesErr
  const wiresErr = checkBijection(iso.wires, aWires, bWires, 'wires')
  if (wiresErr !== null) return wiresErr

  for (const [aId, bId] of iso.regions) {
    const ar = a.regions[aId]!
    const br = b.regions[bId]!
    if (ar.kind !== br.kind) return `region '${aId}' kind '${ar.kind}' does not match '${bId}' kind '${br.kind}'`
    if (ar.kind === 'cut' && br.kind === 'cut') {
      const mappedParent = iso.regions.get(ar.parent)
      if (mappedParent !== br.parent) {
        return `region '${aId}' parent does not transport to region '${bId}' parent`
      }
    }
  }

  for (const [aId, bId] of iso.nodes) {
    const an = a.nodes[aId]!
    const bn = b.nodes[bId]!
    if (an.kind !== bn.kind) return `node '${aId}' kind '${an.kind}' does not match '${bId}' kind '${bn.kind}'`
    const mappedRegion = iso.regions.get(an.region)
    if (mappedRegion !== bn.region) return `node '${aId}' region does not transport to node '${bId}' region`
    switch (an.kind) {
      case 'term':
        if (bn.kind === 'term') {
          if (an.freeArity !== bn.freeArity) {
            return `term '${aId}' freeArity ${an.freeArity} does not match '${bId}' freeArity ${bn.freeArity}`
          }
          if (serializeTerm(an.term) !== serializeTerm(bn.term)) {
            return `term '${aId}' structure does not match '${bId}' structure`
          }
        }
        break
      case 'atom':
        if (bn.kind === 'atom' && !sigEquals(an.sig, bn.sig)) {
          return `atom '${aId}' sig does not match '${bId}' sig`
        }
        break
      case 'ref':
        if (bn.kind === 'ref') {
          if (an.defId !== bn.defId) return `ref '${aId}' defId '${an.defId}' does not match '${bId}' defId '${bn.defId}'`
          if (!sigEquals(an.sig, bn.sig)) return `ref '${aId}' sig does not match '${bId}' sig`
        }
        break
      case 'identity':
        if (bn.kind === 'identity') {
          if (!sigEquals(an.sig, bn.sig)) return `identity '${aId}' sig does not match '${bId}' sig`
          if (an.arity !== bn.arity) return `identity '${aId}' arity ${an.arity} does not match '${bId}' arity ${bn.arity}`
        }
        break
    }
  }

  for (const [aId, bId] of iso.wires) {
    const aw = a.wires[aId]!
    const bw = b.wires[bId]!
    if (!sigEquals(aw.sig, bw.sig)) return `wire '${aId}' sig does not match '${bId}' sig`
    const aEnds = aw.endpoints.map((ep) => {
      const mappedNode = iso.nodes.get(ep.node)
      if (mappedNode === undefined) throw new DiagramError(`wire '${aId}' endpoint node '${ep.node}' has no image`)
      return `${mappedNode}|${endpointPositionKey(a, ep)}`
    }).sort()
    const bEnds = bw.endpoints.map((ep) => `${ep.node}|${endpointPositionKey(b, ep)}`).sort()
    if (aEnds.length !== bEnds.length || aEnds.some((k, i) => k !== bEnds[i])) {
      return `wire '${aId}' endpoints do not transport to wire '${bId}' endpoints`
    }
  }

  for (let i = 0; i < aPins.length; i++) {
    const mapped = iso.wires.get(aPins[i]!)
    if (mapped !== bPins[i]) {
      return `pin ${i}: wire '${aPins[i]}' maps to '${String(mapped)}', expected '${bPins[i]}'`
    }
  }

  return null
}
