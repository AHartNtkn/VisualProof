// Spike4 engine: the in-tree DerivationCursor + kOpen (K-trick mint for OPEN
// terms; closed mints use cursor.intro = closedTermIntro directly).
import { parseTerm } from '../../../../../src/kernel/term/parse'
import type { Term } from '../../../../../src/kernel/term/term'
import { app, lam } from '../../../../../src/kernel/term/term'
import type { ConversionCertificate } from '../../../../../src/kernel/term/certificate'
import { DerivationCursor } from '../../../../../src/theories/macros'
import type { ProofStep, ProofContext } from '../../../../../src/kernel/proof/step'
import type { Diagram, NodeId, RegionId, WireId } from '../../../../../src/kernel/diagram/diagram'

export const consts = new Set(['ZERO', 'SUCC', 'PLUS'])
export const p = (s: string) => parseTerm(s, consts)
export const idCert: ConversionCertificate = { leftSteps: [], rightSteps: [] }

export class E extends DerivationCursor {
  quiet: boolean
  constructor(d: Diagram, ctx: ProofContext, quiet = true) {
    super(d, ctx)
    this.quiet = quiet
  }
  override push(label: string, s: ProofStep): void {
    super.push(label, s)
    if (!this.quiet) console.log(`  ${label} (${s.rule}): ok`)
  }
  /** K-trick: mint a node carrying OPEN term s (frees wired per attach) in `region`, off closed seed. */
  kOpen(tag: string, seed: NodeId, region: RegionId, s: Term, attach: Record<string, WireId>): NodeId {
    const seedTerm = this.termOf(seed)
    this.pushConv(`${tag} K-expand`, seed, app(lam(seedTerm), s), attach)
    const before = this.cur
    this.push(`${tag} fission`, { rule: 'fission', node: seed, path: ['arg'] })
    const made = this.newNodeIn(region, before)
    this.pushConv(`${tag} K-restore`, seed, seedTerm)
    return made
  }
  /** The term node in `region` carrying `t` whose freeVar `name` rides `wire`. */
  nodeOnWire(region: RegionId, t: Term, name: string, wire: WireId): NodeId {
    const J = JSON.stringify
    const found = Object.entries(this.cur.nodes).find(
      ([id, n]) => n.kind === 'term' && n.region === region && J(n.term) === J(t) &&
        this.cur.wires[wire]!.endpoints.some(
          (ep) => ep.node === id && ep.port.kind === 'freeVar' && ep.port.name === name,
        ),
    )
    if (found === undefined) throw new Error(`no '${name}'-on-'${wire}' node in '${region}'`)
    return found[0]
  }
}
