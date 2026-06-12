import type { Term } from '../kernel/term/term'
import { app, lam, termEq } from '../kernel/term/term'
import { applyConversion } from '../kernel/rules/conversion'
import type { Diagram, NodeId, RegionId, WireId } from '../kernel/diagram/diagram'
import type { DiagramWithBoundary } from '../kernel/diagram/boundary'
import { mkSelection, type SubgraphSelection } from '../kernel/diagram/subgraph/selection'
import { extractSubgraph } from '../kernel/diagram/subgraph/extract'
import { replayProof, type ProofContext, type ProofStep } from '../kernel/proof/step'

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
  readonly steps: ProofStep[] = []
  readonly ctx: ProofContext

  constructor(d: Diagram, ctx: ProofContext) {
    this.cur = d
    this.ctx = ctx
  }

  /** Apply one step and record it; a gate rejection rethrows as `step 'label' (rule) failed`. */
  push(label: string, s: ProofStep): void {
    let next: Diagram
    try {
      next = replayProof(this.cur, [s], this.ctx)
    } catch (e) {
      throw new Error(`step '${label}' (${s.rule}) failed: ${e instanceof Error ? e.message : String(e)}`)
    }
    this.cur = next
    this.steps.push(s)
  }

  /**
   * Convert a node's term interactively and record the certificate-carrying
   * step, so the stored derivation replays fuel-free. `attach` names the
   * existing wires the replacement term's new free ports land on; unnamed
   * new ports get fresh singleton wires.
   */
  pushConv(label: string, node: NodeId, t: Term, attach: Readonly<Record<string, WireId>> = {}): void {
    let certificate
    try {
      certificate = applyConversion(this.cur, node, t, CONVERSION_FUEL, attach).certificate
    } catch (e) {
      throw new Error(`step '${label}' (conversion) failed: ${e instanceof Error ? e.message : String(e)}`)
    }
    this.push(label, { rule: 'conversion', node, term: t, certificate, attachments: attach })
  }

  /**
   * K-trick materializer: mint a node carrying term `s` in the seed's region,
   * riding a fresh singleton output wire. The seed (any term node t already
   * there) is converted to `(λu. t) s` — βη-equal, the binder is vacuous —
   * fissioned at ['arg'] to split `s` onto its own node, then converted back.
   * Conversion and fission are equivalences, so this works at any polarity.
   * Free ports of `s` attach to the wires named in `attach`; unnamed ones get
   * fresh singleton wires. Three steps under the given tag.
   */
  kMat(tag: string, seed: NodeId, s: Term, attach: Readonly<Record<string, WireId>>): NodeId {
    const seedTerm = this.termOf(seed)
    const region = this.regionOf(seed)
    this.pushConv(`${tag} K-expand`, seed, app(lam(seedTerm), s), attach)
    const before = this.cur
    this.push(`${tag} fission`, { rule: 'fission', node: seed, path: ['arg'] })
    const made = this.newNodeIn(region, before)
    this.pushConv(`${tag} K-restore`, seed, seedTerm)
    return made
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

/**
 * Live extraction: copy a derived subgraph out of `d` as a self-contained
 * insertion pattern. Derivations prove a fact once, extract it, and insert
 * the copy wherever insertion's polarity gate allows. The selection must be
 * CLOSED — no touching wires, no externally bound atoms — because an open
 * extraction would need attachments or binder bindings the insertion site
 * cannot supply; a closed one inserts with empty attachments and binders.
 */
export function extractClosedPattern(d: Diagram, sel: SubgraphSelection): DiagramWithBoundary {
  const ex = extractSubgraph(d, mkSelection(d, sel))
  if (ex.attachments.length > 0) {
    throw new Error(`extraction is open: touching wires [${ex.attachments.join(', ')}] would need attachments at the insertion site`)
  }
  if (ex.binderStubs.length > 0) {
    throw new Error(`extraction is open: external binders [${ex.binderAttachments.join(', ')}] would need binder bindings at the insertion site`)
  }
  return ex.pattern
}
