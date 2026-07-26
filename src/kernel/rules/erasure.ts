import type { Diagram, Endpoint, Wire, WireId } from '../diagram/diagram'
import { DiagramError, mkDiagram, portKey } from '../diagram/diagram'
import { polarity } from '../diagram/regions'
import type { SubgraphSelection } from '../diagram/subgraph/selection'
import { removeSubgraph } from '../diagram/subgraph/splice'
import { freshId, type IdReservation } from '../diagram/subgraph/freshId'
import { RuleError } from './error'

/** Ordinary erasure deletes any selected subgraph from a positive region.
 * Negative insertion is owned by concrete insertion rules; there is no
 * backward-erasure insertion API. */
export function applyErasure(
  d: Diagram,
  sel: SubgraphSelection,
  orientation: 'forward' | 'backward' = 'forward',
): Diagram {
  if (orientation === 'backward') {
    throw new RuleError('backward erasure is not supported; erasure is forward-only')
  }
  const need = 'positive'
  const have = polarity(d, sel.region)
  if (have !== need) {
    throw new RuleError(`erasure requires a ${need} region; '${sel.region}' is ${have}`)
  }
  return removeSubgraph(d, sel)
}

/**
 * Sever a wire by splitting its endpoints into the kept group (staying on the
 * original wire) and the rest (moving to a fresh wire at the same scope).
 * Replaces `φ(x,x)` by the weaker `∃y φ(x,y)` at the wire's scope, so the
 * scope must be POSITIVE.
 */
export function applyWireSever(d: Diagram, wireId: WireId, keep: readonly Endpoint[], orientation: 'forward' | 'backward' = 'forward', reservation?: IdReservation): Diagram {
  const w = d.wires[wireId]
  if (w === undefined) throw new DiagramError(`unknown wire '${wireId}'`)
  const need = orientation === 'forward' ? 'positive' : 'negative'
  const haveScope = polarity(d, w.scope)
  if (haveScope !== need) {
    throw new RuleError(`${orientation === 'backward' ? 'backward ' : ''}severing a wire requires a ${need} scope; '${w.scope}' is ${haveScope}`)
  }
  const has = (eps: readonly Endpoint[], ep: Endpoint): boolean =>
    eps.some((e) => e.node === ep.node && portKey(e.port) === portKey(ep.port))
  for (const k of keep) {
    if (!has(w.endpoints, k)) {
      throw new RuleError(`endpoint '${k.node}'/'${portKey(k.port)}' is not an endpoint of wire '${wireId}'`)
    }
  }
  const kept = w.endpoints.filter((ep) => has(keep, ep))
  const moved = w.endpoints.filter((ep) => !has(keep, ep))
  const newId = freshId(new Set(Object.keys(d.wires)), `${wireId}_sever`, reservation?.wires)
  const wires: Record<WireId, Wire> = { ...d.wires }
  wires[wireId] = { scope: w.scope, sig: w.sig, endpoints: kept }
  wires[newId] = { scope: w.scope, sig: w.sig, endpoints: moved }
  return mkDiagram({ root: d.root, regions: { ...d.regions }, nodes: { ...d.nodes }, wires })
}
