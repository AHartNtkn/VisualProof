import type { ConversionCertificate } from '../term/certificate'
import { checkConversion } from '../term/certificate'
import type { Diagram, NodeId, Wire, WireId } from '../diagram/diagram'
import { mkDiagram } from '../diagram/diagram'
import { isAncestorOrEqual, cutDepth } from '../diagram/regions'
import { RuleError } from './error'
import { termNodeAt, wireAt } from './access'
import {
  mapTermToCommonCarrier,
  validatePortCorrespondence,
  type PortCorrespondence,
} from './port-correspondence'

/**
 * Rule 9: congruence join — the functionality of equality. Two term nodes in
 * ONE region whose terms are βη-equal (certificate-checked) and whose shared
 * free ports ride identical wires assert equal outputs, and they assert it
 * locally: the region's own content entails o₁ = o₂, so merging the two
 * output wires is an equivalence and needs no polarity gate (like
 * conversion, unlike wireJoin). Free names present in only one term are
 * quantified out by the convertibility and need no wire agreement.
 *
 * The cut-depth gate: each output wire's scope already encloses the nodes'
 * region (mkDiagram invariant), so equal cut depth means no cut lies between
 * scope and region. Bubbles may intervene — they are quantifiers, and ∃
 * commutes with ∃. Without this gate the merge would move a quantifier
 * across a negation that the entailment cannot escape.
 */
export function applyCongruenceJoin(
  d: Diagram,
  a: NodeId,
  b: NodeId,
  certificate: ConversionCertificate,
  correspondence: PortCorrespondence,
): Diagram {
  if (a === b) throw new RuleError(`congruence join needs two distinct nodes; got '${a}' twice`)
  const na = termNodeAt(d, a)
  const nb = termNodeAt(d, b)
  if (na.region !== nb.region) {
    throw new RuleError(
      `congruence join requires both nodes in one region; '${a}' is in '${na.region}', '${b}' in '${nb.region}'`,
    )
  }
  validatePortCorrespondence(correspondence, na.freePorts, nb.freePorts)
  const check = checkConversion(
    mapTermToCommonCarrier(na.term, correspondence.left),
    mapTermToCommonCarrier(nb.term, correspondence.right),
    certificate,
  )
  if (!check.ok) throw new RuleError(`congruence certificate rejected: ${check.reason}`)
  const rightByColumn = new Map<number, string>(
    Object.entries(correspondence.right).map(([name, column]) => [column, name]),
  )
  for (const [leftName, column] of Object.entries(correspondence.left)) {
    const rightName = rightByColumn.get(column)
    if (rightName === undefined) continue
    const wa = wireAt(d, a, { kind: 'freeVar', name: leftName })
    const wb = wireAt(d, b, { kind: 'freeVar', name: rightName })
    if (wa !== wb) {
      throw new RuleError(
        `congruence join requires common column ${column} ports '${leftName}' and '${rightName}' on one wire; found '${wa}' and '${wb}'`,
      )
    }
  }
  const oa = wireAt(d, a, { kind: 'output' })
  const ob = wireAt(d, b, { kind: 'output' })
  if (oa === ob) throw new RuleError(`outputs of '${a}' and '${b}' already share wire '${oa}'`)
  const depth = cutDepth(d, na.region)
  for (const [node, w] of [[a, oa], [b, ob]] as const) {
    const scope = d.wires[w]!.scope
    if (cutDepth(d, scope) !== depth) {
      throw new RuleError(
        `congruence join requires no cut between an output's scope and the nodes' region; wire '${w}' of '${node}' is scoped at '${scope}'`,
      )
    }
  }
  const sa = d.wires[oa]!.scope
  const sb = d.wires[ob]!.scope
  const keep = isAncestorOrEqual(d, sa, sb) ? oa : ob
  const drop = keep === oa ? ob : oa
  const wires: Record<WireId, Wire> = {}
  for (const [id, w] of Object.entries(d.wires)) {
    if (id === drop) continue
    wires[id] = id === keep
      ? { scope: w.scope, endpoints: [...w.endpoints, ...d.wires[drop]!.endpoints] }
      : w
  }
  return mkDiagram({ root: d.root, regions: { ...d.regions }, nodes: { ...d.nodes }, wires })
}
