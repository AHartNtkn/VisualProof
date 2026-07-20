import type { Term } from '../term/term'
import { lam, termEq } from '../term/term'
import type { HeadSpine } from '../term/hnf'
import { headSpine } from '../term/hnf'
import type { Diagram, DiagramNode, NodeId, Wire, WireId } from '../diagram/diagram'
import { mkDiagram } from '../diagram/diagram'
import { freshId, type IdReservation } from '../diagram/subgraph/freshId'
import { RuleError } from './error'
import { termNodeAt, wireAt } from './access'
import {
  mapTermToCommonCarrier,
  validatePortCorrespondence,
  type PortCorrespondence,
} from './port-correspondence'

/**
 * Head strip: decompose an equation between head-normal terms with the same
 * rigid head into the pairwise argument equations.
 *
 * Soundness — decomposition: for terms in head-normal form λx₁…xₙ. h e₁…eₘ
 * the head is rigid — no β/η step can consume it. By Church–Rosser, if two
 * such terms with the same binder count, same head, and same argument count
 * are βη-equal, every common reduct preserves the spine, so corresponding
 * arguments are βη-equal as open terms, hence their prefix-closures are
 * equal.
 *
 * Soundness — polarity-blindness: the rule ADDS the argument equations next
 * to the two co-resident equation nodes. Locally-entailed addition is an
 * equivalence (φ ⟺ φ ∧ ψ when φ ⊢ ψ within the region) — the same
 * justification as congruenceJoin, valid under any polarity. Nothing is
 * removed and no polarity is touched.
 *
 * Only bound heads are rigid under the diagram semantics. A free head is an
 * arbitrary lambda-model individual and may denote a non-injective function,
 * so equality of two applications does not entail equality of their arguments.
 */
export function applyHeadStrip(
  d: Diagram,
  a: NodeId,
  b: NodeId,
  correspondence: PortCorrespondence,
  reservation?: IdReservation,
): Diagram {
  // Gate 1: distinct term nodes in one region.
  if (a === b) throw new RuleError(`head strip needs two distinct nodes; got '${a}' twice`)
  const na = termNodeAt(d, a)
  const nb = termNodeAt(d, b)
  if (na.region !== nb.region) {
    throw new RuleError(
      `head strip requires both nodes in one region; '${a}' is in '${na.region}', '${b}' in '${nb.region}'`,
    )
  }
  const region = na.region
  validatePortCorrespondence(correspondence, na.freePorts, nb.freePorts)

  // Gate 2: the outputs share ONE wire — that is what makes the pair an equation.
  const oa = wireAt(d, a, { kind: 'output' })
  const ob = wireAt(d, b, { kind: 'output' })
  if (oa !== ob) {
    throw new RuleError(
      `head strip requires the outputs of '${a}' and '${b}' to share one wire (an equation); found '${oa}' and '${ob}'`,
    )
  }

  // Gate 3: both terms are in head-normal form.
  const normalHead = (node: NodeId, s: HeadSpine): Extract<HeadSpine['head'], { kind: 'bound' | 'free' }> => {
    if (s.head.kind === 'redex') {
      throw new RuleError(`'${node}' is not in head-normal form; apply the HNF tactic first`)
    }
    return s.head
  }
  const sa = headSpine(na.term)
  const sb = headSpine(nb.term)
  const ha = normalHead(a, sa)
  const hb = normalHead(b, sb)

  // Gate 4: literal spine alignment (η-mismatched spines are the tactic's job).
  if (sa.binders !== sb.binders) {
    throw new RuleError(`head strip requires aligned spines; binder counts differ: ${sa.binders} vs ${sb.binders}`)
  }
  if (sa.args.length !== sb.args.length) {
    throw new RuleError(`head strip requires aligned spines; argument counts differ: ${sa.args.length} vs ${sb.args.length}`)
  }

  // Gate 5: both heads are genuinely rigid bound variables. Free heads are
  // substituted by arbitrary model values and are not injective in general.
  if (ha.kind !== 'bound' || hb.kind !== 'bound') {
    throw new RuleError(`head strip requires bound rigid heads; free heads are not injective`)
  }

  // Gate 6: bound heads correspond by de Bruijn index.
  if (ha.index !== hb.index) {
    throw new RuleError(`heads do not correspond: bound indices differ (${ha.index} vs ${hb.index})`)
  }

  // Gate 7: every correspondence column represented on both sides must name
  // one host wire. One-sided columns impose no attachment constraint.
  const rightByColumn = new Map<number, string>(
    Object.entries(correspondence.right).map(([name, column]) => [column, name]),
  )
  for (const [leftName, column] of Object.entries(correspondence.left)) {
    const rightName = rightByColumn.get(column)
    if (rightName === undefined) continue
    const leftWire = wireAt(d, a, { kind: 'freeVar', name: leftName })
    const rightWire = wireAt(d, b, { kind: 'freeVar', name: rightName })
    if (leftWire !== rightWire) {
      throw new RuleError(
        `head strip shared correspondence column ${column} maps native ports on different host wires ('${leftWire}' and '${rightWire}')`,
      )
    }
  }

  // Gate 8: prefix-closures per position, skipping trivial ones. Wrapping the
  // argument in the same n lambdas keeps its de Bruijn indices into the
  // binder prefix valid and leaves free ports unchanged. A position is
  // trivial exactly when the mapped closures are termEq.
  const closure = (t: Term, n: number): Term => {
    let cur = t
    for (let i = 0; i < n; i++) cur = lam(cur)
    return cur
  }
  const pairs: { ca: Term; cb: Term }[] = []
  for (let i = 0; i < sa.args.length; i++) {
    const ca = closure(sa.args[i]!, sa.binders)
    const cb = closure(sb.args[i]!, sb.binders)
    const mappedLeft = mapTermToCommonCarrier(ca, correspondence.left)
    const mappedRight = mapTermToCommonCarrier(cb, correspondence.right)
    if (termEq(mappedLeft, mappedRight)) continue
    pairs.push({ ca, cb })
  }

  // Step 7: add the equation pairs in R — closures on fresh nodes, each free
  // port riding the wire that port rides on its parent node, outputs sharing
  // one fresh wire scoped at R. The originals stay untouched.
  const nodes: Record<NodeId, DiagramNode> = { ...d.nodes }
  const wires: Record<WireId, Wire> = { ...d.wires }
  const takenNodes = new Set(Object.keys(nodes))
  const takenWires = new Set(Object.keys(wires))
  const attach = (wid: WireId, node: NodeId, name: string): void => {
    const w = wires[wid]!
    wires[wid] = { scope: w.scope, endpoints: [...w.endpoints, { node, port: { kind: 'freeVar', name } }] }
  }
  for (const { ca, cb } of pairs) {
    const ia = freshId(takenNodes, `${a}_hs`, reservation?.nodes)
    takenNodes.add(ia)
    const ib = freshId(takenNodes, `${b}_hs`, reservation?.nodes)
    takenNodes.add(ib)
    nodes[ia] = { kind: 'term', region, term: ca, freePorts: na.freePorts }
    nodes[ib] = { kind: 'term', region, term: cb, freePorts: nb.freePorts }
    for (const name of na.freePorts) attach(wireAt(d, a, { kind: 'freeVar', name }), ia, name)
    for (const name of nb.freePorts) attach(wireAt(d, b, { kind: 'freeVar', name }), ib, name)
    const wo = freshId(takenWires, `${a}_${b}_hs`, reservation?.wires)
    takenWires.add(wo)
    wires[wo] = {
      scope: region,
      endpoints: [
        { node: ia, port: { kind: 'output' } },
        { node: ib, port: { kind: 'output' } },
      ],
    }
  }
  return mkDiagram({ root: d.root, regions: { ...d.regions }, nodes, wires })
}
