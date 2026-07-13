import type { Term } from '../term/term'
import { freePorts } from '../term/term'
import { printTerm } from '../term/print'
import { convertible } from '../term/convert'
import type { ConversionCertificate } from '../term/certificate'
import { checkConversion } from '../term/certificate'
import type { Diagram, DiagramNode, Endpoint, NodeId, Wire, WireId } from '../diagram/diagram'
import { DiagramError, mkDiagram } from '../diagram/diagram'
import { freshId, type IdReservation } from '../diagram/subgraph/freshId'
import { RuleError } from './error'
import { termNodeAt } from './access'

/**
 * Swap a term node's term for a βη-equal one (callers have already verified
 * equality). When t ≈βη t′, any port column absent from t′ was already
 * unconstrained in t (o =βη t ⟺ o =βη t′ pointwise), so detaching a vanished
 * port's endpoint and attaching an added port's endpoint to ANY wire are both
 * equivalences. Vanished ports trim their wires (which survive, possibly
 * endpoint-less); added ports attach to the named wire or a fresh singleton
 * at the node's region.
 */
function replaceNodeTerm(
  d: Diagram,
  nodeId: NodeId,
  node: Extract<DiagramNode, { kind: 'term' }>,
  newTerm: Term,
  attachments: Readonly<Record<string, WireId>>,
  reservation?: IdReservation,
): Diagram {
  const oldPorts = new Set(freePorts(node.term))
  const newPorts = new Set(freePorts(newTerm))
  for (const [name, w] of Object.entries(attachments)) {
    if (oldPorts.has(name) || !newPorts.has(name)) {
      throw new DiagramError(`attachment for port '${name}', which is not a newly added free port of the replacement term`)
    }
    if (d.wires[w] === undefined) throw new DiagramError(`unknown wire '${w}'`)
  }
  const wires: Record<WireId, Wire> = {}
  for (const [id, w] of Object.entries(d.wires)) {
    wires[id] = {
      scope: w.scope,
      endpoints: w.endpoints.filter(
        (ep) => !(ep.node === nodeId && ep.port.kind === 'freeVar' && !newPorts.has(ep.port.name)),
      ),
    }
  }
  for (const name of newPorts) {
    if (oldPorts.has(name)) continue
    const ep: Endpoint = { node: nodeId, port: { kind: 'freeVar', name } }
    const target = attachments[name]
    if (target !== undefined) {
      const w = wires[target]!
      wires[target] = { scope: w.scope, endpoints: [...w.endpoints, ep] }
    } else {
      const fresh = freshId(new Set(Object.keys(wires)), `${nodeId}_${name}`, reservation?.wires)
      wires[fresh] = { scope: node.region, endpoints: [ep] }
    }
  }
  const nodes: Record<NodeId, DiagramNode> = {
    ...d.nodes,
    [nodeId]: { kind: 'term', region: node.region, term: newTerm },
  }
  return mkDiagram({ root: d.root, regions: { ...d.regions }, nodes, wires })
}

export type ConversionResult = {
  readonly diagram: Diagram
  readonly certificate: ConversionCertificate
}

/**
 * Rule 5 (spec §3.1), interactive form: replace a node's term by a
 * βη-convertible one, searching under the fuel budget. Equivalence — no
 * polarity gate. The certificate is returned for proof storage (§3.7).
 */
export function applyConversion(
  d: Diagram,
  nodeId: NodeId,
  newTerm: Term,
  fuel: number,
  attachments: Readonly<Record<string, WireId>> = {},
  reservation?: IdReservation,
): ConversionResult {
  const node = termNodeAt(d, nodeId)
  const r = convertible(node.term, newTerm, fuel)
  if (r.status === 'fuel-exhausted') {
    throw new RuleError(`conversion is undecided under fuel ${fuel}: ${r.detail}; supply a certificate or raise the fuel`)
  }
  if (r.status === 'not-convertible') {
    throw new RuleError(`'${printTerm(node.term)}' and '${printTerm(newTerm)}' are not βη-convertible`)
  }
  return { diagram: replaceNodeTerm(d, nodeId, node, newTerm, attachments, reservation), certificate: r.certificate }
}

/** Rule 5, replay form: fuel-free, checks a stored certificate mechanically. */
export function applyConversionByCertificate(
  d: Diagram,
  nodeId: NodeId,
  newTerm: Term,
  certificate: ConversionCertificate,
  attachments: Readonly<Record<string, WireId>> = {},
  reservation?: IdReservation,
): Diagram {
  const node = termNodeAt(d, nodeId)
  const check = checkConversion(node.term, newTerm, certificate)
  if (!check.ok) throw new RuleError(`conversion certificate rejected: ${check.reason}`)
  return replaceNodeTerm(d, nodeId, node, newTerm, attachments, reservation)
}
