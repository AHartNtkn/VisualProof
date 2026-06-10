import type { Diagram, Endpoint, Wire, WireId } from '../diagram/diagram'
import { DiagramError, mkDiagram, portKey } from '../diagram/diagram'
import { polarity } from '../diagram/regions'
import type { SubgraphSelection } from '../diagram/subgraph/selection'
import { removeSubgraph } from '../diagram/subgraph/splice'
import { freshId } from '../diagram/subgraph/freshId'
import { RuleError } from './error'

/** Rule 2a (spec §3.1): delete any subgraph from a POSITIVE region. */
export function applyErasure(d: Diagram, sel: SubgraphSelection): Diagram {
  if (polarity(d, sel.region) !== 'positive') {
    throw new RuleError(`erasure requires a positive region; '${sel.region}' is negative`)
  }
  return removeSubgraph(d, sel)
}

/**
 * Rule 2b: sever a wire — split its endpoints into the kept group (staying on
 * the original wire) and the rest (moving to a fresh wire at the same scope).
 * Replaces `φ(x,x)` by the weaker `∃y φ(x,y)` at the wire's scope, so the
 * scope must be POSITIVE.
 */
export function applyWireSever(d: Diagram, wireId: WireId, keep: readonly Endpoint[]): Diagram {
  const w = d.wires[wireId]
  if (w === undefined) throw new DiagramError(`unknown wire '${wireId}'`)
  if (polarity(d, w.scope) !== 'positive') {
    throw new RuleError(`severing a wire requires a positive scope; '${w.scope}' is negative`)
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
  const newId = freshId(new Set(Object.keys(d.wires)), `${wireId}_sever`)
  const wires: Record<WireId, Wire> = { ...d.wires }
  wires[wireId] = { scope: w.scope, endpoints: kept }
  wires[newId] = { scope: w.scope, endpoints: moved }
  return mkDiagram({ root: d.root, regions: { ...d.regions }, nodes: { ...d.nodes }, wires })
}
