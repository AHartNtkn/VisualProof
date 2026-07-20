import type { Term } from '../kernel/term/term'
import { termEq } from '../kernel/term/term'
import { applyConversion } from '../kernel/rules/conversion'
import { findDeiterationEvidence } from '../kernel/rules/iteration'
import type { Diagram, NodeId, RegionId, WireId } from '../kernel/diagram/diagram'
import { type ProofContext, type ProofStep } from '../kernel/proof/step'
import { applyAction, singleStepAction, type ProofAction } from '../kernel/proof/action'
import type { ConversionCertificate } from '../kernel/term/certificate'
import { termNodeAt } from '../kernel/rules/access'
import { proposePortCorrespondence } from '../kernel/rules/port-correspondence'

/**
 * Interactive conversion fuel for derivation construction. Conversions made
 * through the cursor are small K-trick redexes and definitional reshuffles,
 * far below this budget. Build-time only: the recorded step carries the
 * certificate, so replay (verifyTheory, loadTheory) is fuel-free; exhaustion
 * throws a loud RuleError naming the budget.
 */
const CONVERSION_FUEL = 8192

/**
 * Replay cursor for building derivations: each push applies the step through
 * the real kernel appliers (replayProof carries no trust) and tracks the
 * current diagram, so the finder helpers can locate the ids fresh steps mint.
 * A failing step throws with its label and leaves the cursor untouched.
 */
export class DerivationCursor {
  cur: Diagram
  readonly actions: ProofAction[] = []
  readonly ctx: ProofContext

  constructor(d: Diagram, ctx: ProofContext) {
    this.cur = d
    this.ctx = ctx
  }

  /** Apply one step and record it; a gate rejection rethrows as `step 'label' (rule) failed`. */
  push(label: string, s: ProofStep): void {
    let next: Diagram
    try {
      next = applyAction(this.cur, singleStepAction(label, s), this.ctx)
    } catch (e) {
      throw new Error(`step '${label}' (${s.rule}) failed: ${e instanceof Error ? e.message : String(e)}`)
    }
    this.cur = next
    this.actions.push(singleStepAction(label, s))
  }

  /**
   * Convert a node's term interactively and record the certificate-carrying
   * step, so the stored derivation replays fuel-free. `attach` names the
   * existing wires the replacement term's new free ports land on; unnamed
   * new ports get fresh singleton wires.
   */
  pushConv(label: string, node: NodeId, t: Term, attach: Readonly<Record<string, WireId>> = {}): void {
    let certificate
    const correspondence = proposePortCorrespondence(termNodeAt(this.cur, node).term, t)
    try {
      certificate = applyConversion(this.cur, node, t, correspondence, CONVERSION_FUEL, attach).certificate
    } catch (e) {
      throw new Error(`step '${label}' (conversion) failed: ${e instanceof Error ? e.message : String(e)}`)
    }
    this.push(label, { rule: 'conversion', node, term: t, certificate, correspondence, attachments: attach })
  }

  pushCongruence(label: string, a: NodeId, b: NodeId, certificate: ConversionCertificate): void {
    const correspondence = proposePortCorrespondence(termNodeAt(this.cur, a).term, termNodeAt(this.cur, b).term)
    this.push(label, { rule: 'congruenceJoin', a, b, certificate, correspondence })
  }

  /** Search while constructing the theory, then store only the chosen checked evidence. */
  pushDeiteration(label: string, selection: import('../kernel/diagram/subgraph/selection').SubgraphSelection, fuel = 8192): void {
    const evidence = findDeiterationEvidence(this.cur, selection, fuel)
    this.push(label, { rule: 'deiteration', sel: selection, ...evidence })
  }

  /**
   * Introduce a closed term node in `region` on a fresh singleton output
   * wire (one closedTermIntro step) and return the minted node's id.
   */
  intro(tag: string, region: RegionId, t: Term): NodeId {
    const before = this.cur
    this.push(tag, { rule: 'closedTermIntro', region, term: t })
    return this.newNodeIn(region, before, t)
  }

  spawnOpenTerm(tag: string, region: RegionId, term: Term): NodeId {
    const before = this.cur
    this.push(tag, { rule: 'openTermSpawn', region, term })
    return this.newNodeIn(region, before, term)
  }

  spawnRelation(tag: string, region: RegionId, defId: string): NodeId {
    const relation = this.ctx.relations.get(defId)
    if (relation === undefined) throw new Error(`unknown relation '${defId}'`)
    const before = this.cur
    this.push(tag, { rule: 'relationSpawn', region, defId, arity: relation.boundary.length })
    const found = Object.entries(this.cur.nodes).find(([id, node]) =>
      node.kind === 'ref' && node.region === region && node.defId === defId && before.nodes[id] === undefined)
    if (found === undefined) throw new Error(`no new '${defId}' relation appeared in region '${region}'`)
    return found[0]
  }

  spawnBoundRelation(tag: string, region: RegionId, binder: RegionId): NodeId {
    const value = this.cur.regions[binder]
    if (value === undefined || value.kind !== 'bubble') throw new Error(`bound relation binder '${binder}' is not a bubble`)
    const before = this.cur
    this.push(tag, { rule: 'boundRelationSpawn', region, binder, arity: value.arity })
    const found = Object.entries(this.cur.nodes).find(([id, node]) =>
      node.kind === 'atom' && node.region === region && node.binder === binder && before.nodes[id] === undefined)
    if (found === undefined) throw new Error(`no new bound relation appeared in region '${region}'`)
    return found[0]
  }

  /** The cut that appeared directly under `parent` since the `before` snapshot. */
  newCutIn(parent: RegionId, before: Diagram): RegionId {
    const found = Object.entries(this.cur.regions).find(
      ([id, r]) => r.kind === 'cut' && r.parent === parent && before.regions[id] === undefined,
    )
    if (found === undefined) throw new Error(`no cut appeared under region '${parent}'`)
    return found[0]
  }

  /** The term node that appeared in `region` since `before`, optionally filtered by term. */
  newNodeIn(region: RegionId, before: Diagram, term?: Term): NodeId {
    const found = Object.entries(this.cur.nodes).find(
      ([id, n]) => n.kind === 'term' && n.region === region && before.nodes[id] === undefined &&
        (term === undefined || termEq(n.term, term)),
    )
    if (found === undefined) throw new Error(`no new term node appeared in region '${region}'`)
    return found[0]
  }

  /** The term node in `region` carrying exactly `t`. */
  nodeBy(region: RegionId, t: Term): NodeId {
    const found = Object.entries(this.cur.nodes).find(
      ([, n]) => n.kind === 'term' && n.region === region && termEq(n.term, t),
    )
    if (found === undefined) throw new Error(`no term node carrying the given term in region '${region}'`)
    return found[0]
  }

  /** The term carried by `node`. */
  termOf(node: NodeId): Term {
    const n = this.cur.nodes[node]
    if (n === undefined || n.kind !== 'term') throw new Error(`'${node}' is not a term node`)
    return n.term
  }

  /** The region holding `node`. */
  regionOf(node: NodeId): RegionId {
    const n = this.cur.nodes[node]
    if (n === undefined) throw new Error(`unknown node '${node}'`)
    return n.region
  }

  /** The wire holding `node`'s output or named free-variable endpoint. */
  wireOf(node: NodeId, kind: 'output' | 'freeVar', name?: string): WireId {
    const found = Object.entries(this.cur.wires).find(([, w]) =>
      w.endpoints.some((ep) => ep.node === node && ep.port.kind === kind &&
        (name === undefined || (ep.port.kind === 'freeVar' && ep.port.name === name))))
    if (found === undefined) {
      throw new Error(`node '${node}' has no ${kind}${name === undefined ? '' : ` '${name}'`} endpoint on any wire`)
    }
    return found[0]
  }
}
