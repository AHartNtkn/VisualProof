// Shared engine for plusComm spike: replay cursor + helpers from rooted.ts.
import { parseTerm } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/term/parse'
import type { Term } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/term/term'
import { app, lam } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/term/term'
import { applyConversion } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/rules/conversion'
import type { ConversionCertificate } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/term/certificate'
import { replayProof, type ProofContext, type ProofStep } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/proof/step'
import type { Diagram, NodeId, RegionId, WireId } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/diagram/diagram'

export const consts = new Set(['ZERO', 'SUCC', 'PLUS'])
export const p = (s: string) => parseTerm(s, consts)
export const idCert: ConversionCertificate = { leftSteps: [], rightSteps: [] }
const J = (t: Term) => JSON.stringify(t)

export class Eng {
  cur: Diagram
  steps: ProofStep[] = []
  ctx: ProofContext
  quiet: boolean
  constructor(d: Diagram, ctx: ProofContext, quiet = false) {
    this.cur = d
    this.ctx = ctx
    this.quiet = quiet
  }
  push(label: string, s: ProofStep): void {
    this.steps.push(s)
    this.cur = replayProof(this.cur, [s], this.ctx)
    if (!this.quiet) console.log(`  ${label} (${s.rule}): ok`)
  }
  newCutIn(parent: RegionId, before: Diagram): RegionId {
    return Object.entries(this.cur.regions).find(
      ([id, r]) => r.kind === 'cut' && r.parent === parent && before.regions[id] === undefined,
    )![0]
  }
  newNodeIn(region: RegionId, before: Diagram, term?: Term): NodeId {
    return Object.entries(this.cur.nodes).find(
      ([id, n]) => n.kind === 'term' && n.region === region && before.nodes[id] === undefined &&
        (term === undefined || J(n.term) === J(term)),
    )![0]
  }
  nodeBy(region: RegionId, t: Term): NodeId {
    return Object.entries(this.cur.nodes).find(
      ([, n]) => n.kind === 'term' && n.region === region && J(n.term) === J(t),
    )![0]
  }
  termOf(node: NodeId): Term {
    return (this.cur.nodes[node] as { term: Term }).term
  }
  wireOf(node: NodeId, kind: 'output' | 'freeVar', name?: string): WireId {
    return Object.entries(this.cur.wires).find(([, w]) =>
      w.endpoints.some((ep) => ep.node === node && ep.port.kind === kind &&
        (name === undefined || (ep.port.kind === 'freeVar' && ep.port.name === name))))![0]
  }
  pushConv(label: string, node: NodeId, t: Term, attach: Readonly<Record<string, WireId>> = {}): void {
    const c = applyConversion(this.cur, node, t, 8192, attach)
    this.push(label, { rule: 'conversion', node, term: t, certificate: c.certificate, attachments: attach })
  }
  /** K-trick materializer: mint a node with term s (frees per attach) in region, off a seed node. */
  kMat(tag: string, seed: NodeId, seedTerm: Term, region: RegionId, s: Term, attach: Record<string, WireId>): NodeId {
    const target = app(lam(seedTerm), s)
    this.pushConv(`${tag} K-expand`, seed, target, attach)
    const before = this.cur
    this.push(`${tag} fission`, { rule: 'fission', node: seed, path: ['arg'] })
    const made = this.newNodeIn(region, before)
    this.pushConv(`${tag} K-restore`, seed, seedTerm)
    return made
  }
}
