import type { Term } from '../term/term'
import { lam, termEq, freePorts } from '../term/term'
import type { HeadSpine } from '../term/hnf'
import { headSpine } from '../term/hnf'
import type { Diagram, DiagramNode, NodeId, Wire, WireId } from '../diagram/diagram'
import { mkDiagram } from '../diagram/diagram'
import { freshId, type IdReservation } from '../diagram/subgraph/freshId'
import { RuleError } from './error'
import { termNodeAt, wireAt } from './access'

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
 * Name-blindness: heads correspond by bound de Bruijn INDEX or by the WIRE
 * their free head ports ride — never by port name, which is plumbing, not
 * semantics.
 */
export function applyHeadStrip(d: Diagram, a: NodeId, b: NodeId, reservation?: IdReservation): Diagram {
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

  // Gate 2: the outputs share ONE wire — that is what makes the pair an equation.
  const oa = wireAt(d, a, { kind: 'output' })
  const ob = wireAt(d, b, { kind: 'output' })
  if (oa !== ob) {
    throw new RuleError(
      `head strip requires the outputs of '${a}' and '${b}' to share one wire (an equation); found '${oa}' and '${ob}'`,
    )
  }

  // Gate 3: both heads rigid (bound or free).
  const rigidHead = (node: NodeId, s: HeadSpine): Extract<HeadSpine['head'], { kind: 'bound' | 'free' }> => {
    if (s.head.kind === 'redex') {
      throw new RuleError(`'${node}' is not in head-normal form; apply the HNF tactic first`)
    }
    return s.head
  }
  const sa = headSpine(na.term)
  const sb = headSpine(nb.term)
  const ha = rigidHead(a, sa)
  const hb = rigidHead(b, sb)

  // Gate 4: literal spine alignment (η-mismatched spines are the tactic's job).
  if (sa.binders !== sb.binders) {
    throw new RuleError(`head strip requires aligned spines; binder counts differ: ${sa.binders} vs ${sb.binders}`)
  }
  if (sa.args.length !== sb.args.length) {
    throw new RuleError(`head strip requires aligned spines; argument counts differ: ${sa.args.length} vs ${sb.args.length}`)
  }

  // Gate 5: heads correspond — equal bound index, or free heads on the SAME wire.
  if (ha.kind === 'bound' || hb.kind === 'bound') {
    if (ha.kind !== 'bound' || hb.kind !== 'bound') {
      throw new RuleError(`heads do not correspond: one head is a bound variable, the other is a free individual`)
    }
    if (ha.index !== hb.index) {
      throw new RuleError(`heads do not correspond: bound indices differ (${ha.index} vs ${hb.index})`)
    }
  } else {
    const wha = wireAt(d, a, { kind: 'freeVar', name: ha.name })
    const whb = wireAt(d, b, { kind: 'freeVar', name: hb.name })
    if (wha !== whb) {
      throw new RuleError(
        `heads do not correspond: the free heads ride different wires ('${wha}' and '${whb}'); they must be one individual`,
      )
    }
  }

  // Gate 6: prefix-closures per position, skipping trivial ones. Wrapping the
  // argument in the same n lambdas keeps its de Bruijn indices into the
  // binder prefix valid and leaves free ports unchanged. A position is
  // trivial exactly when the closures are termEq AND every shared free port
  // rides the same wire in both nodes — then the added conjunct would be
  // derivable by one iteration (exactness, not heuristic).
  const closure = (t: Term, n: number): Term => {
    let cur = t
    for (let i = 0; i < n; i++) cur = lam(cur)
    return cur
  }
  const pairs: { ca: Term; cb: Term }[] = []
  for (let i = 0; i < sa.args.length; i++) {
    const ca = closure(sa.args[i]!, sa.binders)
    const cb = closure(sb.args[i]!, sb.binders)
    if (termEq(ca, cb)) {
      const allShared = freePorts(ca).every(
        (name) => wireAt(d, a, { kind: 'freeVar', name }) === wireAt(d, b, { kind: 'freeVar', name }),
      )
      if (allShared) continue
    }
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
    nodes[ia] = { kind: 'term', region, term: ca }
    nodes[ib] = { kind: 'term', region, term: cb }
    for (const name of freePorts(ca)) attach(wireAt(d, a, { kind: 'freeVar', name }), ia, name)
    for (const name of freePorts(cb)) attach(wireAt(d, b, { kind: 'freeVar', name }), ib, name)
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
