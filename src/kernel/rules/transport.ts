import { freePorts } from '../term/term'
import type { ConversionCertificate } from '../term/certificate'
import { checkConversion } from '../term/certificate'
import type { Diagram, Endpoint, NodeId, Wire, WireId } from '../diagram/diagram'
import { mkDiagram, portKey } from '../diagram/diagram'
import { isAncestorOrEqual } from '../diagram/regions'
import { RuleError } from './error'
import { termNodeAt, wireAt } from './access'

/**
 * Closed-evidence endpoint transport — substituting equals inside their common
 * region. Two term nodes `a`, `b` co-resident in one region R carry CLOSED
 * terms (no free ports) that are βη-equal by replayed certificate. Their output
 * wires therefore provably carry the same closed value inside R
 * (⟦wireA⟧ = ⟦tA⟧ = ⟦tB⟧ = ⟦wireB⟧). A single consumer endpoint riding `a`'s
 * output wire, whose node lies at or inside R, may move to `b`'s output wire:
 * re-attaching a consumer that lives inside R across the two locally-equal
 * lines is an equivalence in both directions.
 *
 * Soundness (congruenceJoin class — locally-entailed equivalence, POLARITY-
 * BLIND). Closedness gives zero binder entanglement: neither value depends on
 * any argument line, so no wire is captured, re-scoped, or created — only one
 * endpoint changes which wire it names. The two evidence lines keep their own
 * scopes forever; nothing is quantifier-moved. That zero-entanglement is why
 * OPEN terms are refused: an open term's value rides its argument lines, and
 * moving a consumer would then interact with those bindings the way wireJoin /
 * insertion regulate. The closed case is the one with no entanglement at all.
 *
 * The at-or-inside-R gate on the endpoint's node is the locality boundary: the
 * equality ⟦wireA⟧ = ⟦wireB⟧ is entailed by R's own content (both nodes sit in
 * R), so only a consumer inside R may rely on it. A consumer above R would not
 * see the equality and moving it would not be an equivalence.
 *
 * Refusals: non-term evidence; open evidence terms; failed certificate;
 * evidence nodes in different regions; the two outputs already sharing a wire;
 * the endpoint not on `a`'s output wire; `a`'s own output as the endpoint; the
 * endpoint's node lying outside R.
 */
export function applyEndpointTransport(
  d: Diagram,
  a: NodeId,
  b: NodeId,
  endpoint: Endpoint,
  certificate: ConversionCertificate,
): Diagram {
  if (a === b) throw new RuleError(`endpoint transport needs two distinct evidence nodes; got '${a}' twice`)
  const na = termNodeAt(d, a)
  const nb = termNodeAt(d, b)
  if (na.region !== nb.region) {
    throw new RuleError(
      `endpoint transport requires both evidence nodes in one region; '${a}' is in '${na.region}', '${b}' in '${nb.region}'`,
    )
  }
  const region = na.region
  const fa = freePorts(na.term)
  if (fa.length > 0) {
    throw new RuleError(`endpoint transport requires closed evidence; '${a}' has free ports [${fa.map((n) => `'${n}'`).join(', ')}]`)
  }
  const fb = freePorts(nb.term)
  if (fb.length > 0) {
    throw new RuleError(`endpoint transport requires closed evidence; '${b}' has free ports [${fb.map((n) => `'${n}'`).join(', ')}]`)
  }
  const check = checkConversion(na.term, nb.term, certificate)
  if (!check.ok) throw new RuleError(`endpoint transport certificate rejected: ${check.reason}`)

  const wA = wireAt(d, a, { kind: 'output' })
  const wB = wireAt(d, b, { kind: 'output' })
  if (wA === wB) {
    throw new RuleError(`evidence outputs of '${a}' and '${b}' already share wire '${wA}'; nothing to transport`)
  }
  const epKey = portKey(endpoint.port)
  if (endpoint.node === a && epKey === portKey({ kind: 'output' })) {
    throw new RuleError(`the transported endpoint may not be evidence node '${a}'s own output`)
  }
  if (!d.wires[wA]!.endpoints.some((ep) => ep.node === endpoint.node && portKey(ep.port) === epKey)) {
    throw new RuleError(`transported endpoint (node '${endpoint.node}', port '${epKey}') is not on '${a}'s output wire '${wA}'`)
  }
  const epNode = d.nodes[endpoint.node]
  if (epNode === undefined) throw new RuleError(`transported endpoint references unknown node '${endpoint.node}'`)
  if (!isAncestorOrEqual(d, region, epNode.region)) {
    throw new RuleError(
      `transported endpoint's node '${endpoint.node}' (region '${epNode.region}') does not lie inside the evidence region '${region}'`,
    )
  }

  const wires: Record<WireId, Wire> = {}
  for (const [id, w] of Object.entries(d.wires)) {
    if (id === wA) {
      wires[id] = { scope: w.scope, endpoints: w.endpoints.filter((ep) => !(ep.node === endpoint.node && portKey(ep.port) === epKey)) }
    } else if (id === wB) {
      wires[id] = { scope: w.scope, endpoints: [...w.endpoints, endpoint] }
    } else {
      wires[id] = w
    }
  }
  return mkDiagram({ root: d.root, regions: { ...d.regions }, nodes: { ...d.nodes }, wires })
}
