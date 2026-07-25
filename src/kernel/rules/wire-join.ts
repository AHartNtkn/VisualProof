import type { Diagram, Wire, WireId } from '../diagram/diagram'
import { DiagramError, mkDiagram } from '../diagram/diagram'
import { isAncestorOrEqual, polarity } from '../diagram/regions'
import { sigEquals, sigKey } from '../diagram/sig'
import { RuleError } from './error'

/**
 * General gated cross-scope merge: join two wires (assert identity of their
 * individuals). This is distinct from the eager identity-node canonicalizer:
 * it authorizes an inference between already-existing wires rather than
 * normalizing stored identity content. Replaces
 * the inner quantifier's content `∃y ψ(y)` by the stronger `ψ(x)`, so the
 * INNER wire's scope must be negative. Scopes must be comparable; the merged
 * wire keeps the outer scope (and the outer wire's id). Only wires of the
 * SAME signature can be identified — asserting x = y presupposes x and y
 * range over the same sort — so mismatched signatures are refused before any
 * scope/polarity reasoning runs.
 */
export function applyWireJoin(d: Diagram, a: WireId, b: WireId, orientation: 'forward' | 'backward' = 'forward'): Diagram {
  const wa = d.wires[a]
  const wb = d.wires[b]
  if (wa === undefined) throw new DiagramError(`unknown wire '${a}'`)
  if (wb === undefined) throw new DiagramError(`unknown wire '${b}'`)
  if (a === b) throw new RuleError(`cannot join a wire with itself ('${a}')`)
  if (!sigEquals(wa.sig, wb.sig)) {
    throw new RuleError(`cannot join wires of different signatures: '${sigKey(wa.sig)}' vs '${sigKey(wb.sig)}'`)
  }
  let outerId: WireId
  let innerId: WireId
  if (isAncestorOrEqual(d, wa.scope, wb.scope)) {
    outerId = a
    innerId = b
  } else if (isAncestorOrEqual(d, wb.scope, wa.scope)) {
    outerId = b
    innerId = a
  } else {
    throw new RuleError(
      `wires '${a}' and '${b}' have incomparable scopes ('${wa.scope}', '${wb.scope}'); iterate one inward first`,
    )
  }
  const inner = d.wires[innerId]!
  const needJoin = orientation === 'forward' ? 'negative' : 'positive'
  const haveJoin = polarity(d, inner.scope)
  if (haveJoin !== needJoin) {
    throw new RuleError(`${orientation === 'backward' ? 'backward ' : ''}joining wires requires the inner wire's scope to be ${needJoin}; '${inner.scope}' is ${haveJoin}`)
  }
  const outer = d.wires[outerId]!
  // The merged wire keeps the OUTER scope: the inner endpoints' regions are
  // enclosed by the inner scope, which the outer scope encloses transitively,
  // so mkDiagram's scope check holds automatically.
  const wires: Record<WireId, Wire> = {}
  for (const [id, w] of Object.entries(d.wires)) {
    if (id === innerId) continue
    wires[id] = id === outerId
      ? { scope: outer.scope, sig: outer.sig, endpoints: [...outer.endpoints, ...inner.endpoints] }
      : w
  }
  // The authoritative constructor normalizes any identity nodes affected by
  // the merge and validates the resulting graph before it crosses the rule
  // boundary.
  return mkDiagram({
    root: d.root,
    regions: { ...d.regions },
    nodes: { ...d.nodes },
    wires,
  })
}
