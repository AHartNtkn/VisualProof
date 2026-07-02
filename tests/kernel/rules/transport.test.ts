import { describe, it, expect } from 'vitest'
import { lam, bvar, port } from '../../../src/kernel/term/term'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import type { Diagram, NodeId, WireId } from '../../../src/kernel/diagram/diagram'
import { applyEndpointTransport } from '../../../src/kernel/rules/transport'
import { boundaryFingerprint } from '../../../src/kernel/diagram/canonical/fingerprint'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { stepToJson, stepFromJson } from '../../../src/kernel/proof/json'
import { applyStep, type ProofStep, type ProofContext } from '../../../src/kernel/proof/step'

const ZEROp = lam(lam(bvar(0)))       // λf x. x
const ONEp = lam(lam(bvar(0)))        // βη-equal spelling of the same closed value
const KI = lam(lam(bvar(1)))          // λf x. f — a DIFFERENT closed value
const idCert = { leftSteps: [], rightSteps: [] }

function outWireOf(d: Diagram, node: NodeId): WireId {
  for (const [id, w] of Object.entries(d.wires)) {
    if (w.endpoints.some((ep) => ep.node === node && ep.port.kind === 'output')) return id
  }
  throw new Error(`no output wire for '${node}'`)
}

/**
 * Two co-resident closed ZERO evidence nodes `a`,`b` in `region`; a consumer
 * term node carrying `port('s0')` whose free port rides a's output wire. The
 * canonical shape every happy-path / polarity test transports across.
 */
function twoEvidence(inCut: boolean) {
  const b = new DiagramBuilder()
  const region = inCut ? b.cut(b.root) : b.root
  const za = b.termNode(region, ZEROp)
  const zb = b.termNode(region, ONEp)
  const cons = b.termNode(region, port('s0'))
  const wA = b.wire(region, [{ node: za, port: { kind: 'output' } }, { node: cons, port: { kind: 'freeVar', name: 's0' } }])
  const wB = b.wire(region, [{ node: zb, port: { kind: 'output' } }])
  const consOut = b.wire(region, [{ node: cons, port: { kind: 'output' } }])
  return { d: b.build(), region, za, zb, cons, wA, wB, consOut }
}

describe('endpoint transport — happy path', () => {
  it('moves a consumer endpoint from a-line to b-line (positive region)', () => {
    const s = twoEvidence(false)
    const out = applyEndpointTransport(s.d, s.za, s.zb, { node: s.cons, port: { kind: 'freeVar', name: 's0' } }, idCert)
    // the consumer's free port now rides b's output wire, not a's
    const wA = outWireOf(out, s.za)
    const wB = outWireOf(out, s.zb)
    expect(out.wires[wA]!.endpoints.some((ep) => ep.node === s.cons)).toBe(false)
    expect(out.wires[wB]!.endpoints.some((ep) => ep.node === s.cons && ep.port.kind === 'freeVar')).toBe(true)
  })

  it('is polarity-blind — same transport inside a negative cut', () => {
    const s = twoEvidence(true)
    const out = applyEndpointTransport(s.d, s.za, s.zb, { node: s.cons, port: { kind: 'freeVar', name: 's0' } }, idCert)
    const wB = outWireOf(out, s.zb)
    expect(out.wires[wB]!.endpoints.some((ep) => ep.node === s.cons && ep.port.kind === 'freeVar')).toBe(true)
  })
})

describe('endpoint transport — refusals (each message observed)', () => {
  it('refuses two identical node ids', () => {
    const s = twoEvidence(false)
    expect(() => applyEndpointTransport(s.d, s.za, s.za, { node: s.cons, port: { kind: 'freeVar', name: 's0' } }, idCert))
      .toThrow(/two distinct evidence nodes/)
  })

  it('refuses a non-term evidence node (a ref)', () => {
    const b = new DiagramBuilder()
    const r = b.ref(b.root, 'zero', 1)
    const zb = b.termNode(b.root, ZEROp)
    const cons = b.termNode(b.root, port('s0'))
    b.wire(b.root, [{ node: r, port: { kind: 'arg', index: 0 } }, { node: cons, port: { kind: 'freeVar', name: 's0' } }])
    b.wire(b.root, [{ node: zb, port: { kind: 'output' } }])
    const d = b.build()
    expect(() => applyEndpointTransport(d, r, zb, { node: cons, port: { kind: 'freeVar', name: 's0' } }, idCert))
      .toThrow(/applies to term nodes/)
  })

  it('refuses evidence nodes in different regions', () => {
    const b = new DiagramBuilder()
    const za = b.termNode(b.root, ZEROp)
    const cut = b.cut(b.root)
    const zb = b.termNode(cut, ZEROp)
    const cons = b.termNode(b.root, port('s0'))
    b.wire(b.root, [{ node: za, port: { kind: 'output' } }, { node: cons, port: { kind: 'freeVar', name: 's0' } }])
    b.wire(b.root, [{ node: zb, port: { kind: 'output' } }])
    const d = b.build()
    expect(() => applyEndpointTransport(d, za, zb, { node: cons, port: { kind: 'freeVar', name: 's0' } }, idCert))
      .toThrow(/both evidence nodes in one region/)
  })

  it('GATE-MUTATION PROBE — refuses OPEN evidence (soundness: open value rides its args)', () => {
    // `a` carries an OPEN term `f x`; its value depends on the f,x lines, so
    // transporting a consumer across it is NOT a closed-value equivalence.
    const b = new DiagramBuilder()
    const za = b.termNode(b.root, port('s0'))            // open: free port s0
    const zb = b.termNode(b.root, port('s0'))
    const cons = b.termNode(b.root, port('s1'))
    b.wire(b.root, [{ node: za, port: { kind: 'output' } }, { node: cons, port: { kind: 'freeVar', name: 's1' } }])
    b.wire(b.root, [{ node: za, port: { kind: 'freeVar', name: 's0' } }, { node: zb, port: { kind: 'freeVar', name: 's0' } }])
    b.wire(b.root, [{ node: zb, port: { kind: 'output' } }])
    const d = b.build()
    // If the closedness gate is dropped, this transport would succeed — the
    // probe asserts it is refused, so a mutation deleting the gate fails here.
    expect(() => applyEndpointTransport(d, za, zb, { node: cons, port: { kind: 'freeVar', name: 's1' } }, idCert))
      .toThrow(/requires closed evidence/)
  })

  it('refuses a rejected certificate (distinct closed values)', () => {
    const b = new DiagramBuilder()
    const za = b.termNode(b.root, ZEROp)
    const zb = b.termNode(b.root, KI)     // λf x. f ≠βη λf x. x
    const cons = b.termNode(b.root, port('s0'))
    b.wire(b.root, [{ node: za, port: { kind: 'output' } }, { node: cons, port: { kind: 'freeVar', name: 's0' } }])
    b.wire(b.root, [{ node: zb, port: { kind: 'output' } }])
    const d = b.build()
    expect(() => applyEndpointTransport(d, za, zb, { node: cons, port: { kind: 'freeVar', name: 's0' } }, idCert))
      .toThrow(/certificate rejected/)
  })

  it('refuses when the two outputs already share a wire', () => {
    const b = new DiagramBuilder()
    const za = b.termNode(b.root, ZEROp)
    const zb = b.termNode(b.root, ONEp)
    const cons = b.termNode(b.root, port('s0'))
    b.wire(b.root, [
      { node: za, port: { kind: 'output' } },
      { node: zb, port: { kind: 'output' } },
      { node: cons, port: { kind: 'freeVar', name: 's0' } },
    ])
    const d = b.build()
    expect(() => applyEndpointTransport(d, za, zb, { node: cons, port: { kind: 'freeVar', name: 's0' } }, idCert))
      .toThrow(/already share wire/)
  })

  it("refuses the evidence node's own output as the endpoint", () => {
    const s = twoEvidence(false)
    expect(() => applyEndpointTransport(s.d, s.za, s.zb, { node: s.za, port: { kind: 'output' } }, idCert))
      .toThrow(/may not be evidence node/)
  })

  it("refuses an endpoint not on a's output wire", () => {
    const s = twoEvidence(false)
    // the consumer's OWN output endpoint rides consOut, not wA
    expect(() => applyEndpointTransport(s.d, s.za, s.zb, { node: s.cons, port: { kind: 'output' } }, idCert))
      .toThrow(/is not on/)
  })

  it("refuses a consumer node lying outside the evidence region", () => {
    // evidence in a cut; the consumer at the root (above the cut) rides a's
    // root-scoped output wire — it cannot see the in-cut equality.
    const b = new DiagramBuilder()
    const cut = b.cut(b.root)
    const za = b.termNode(cut, ZEROp)
    const zb = b.termNode(cut, ONEp)
    const cons = b.termNode(b.root, port('s0'))
    const wA = b.wire(b.root, [{ node: za, port: { kind: 'output' } }, { node: cons, port: { kind: 'freeVar', name: 's0' } }])
    b.wire(cut, [{ node: zb, port: { kind: 'output' } }])
    const d = b.build()
    void wA
    expect(() => applyEndpointTransport(d, za, zb, { node: cons, port: { kind: 'freeVar', name: 's0' } }, idCert))
      .toThrow(/does not lie inside the evidence region/)
  })
})

describe('endpoint transport — JSON round-trip', () => {
  it('serializes and replays to the same diagram', () => {
    const s = twoEvidence(false)
    const step: ProofStep = {
      rule: 'endpointTransport', a: s.za, b: s.zb,
      endpoint: { node: s.cons, port: { kind: 'freeVar', name: 's0' } }, certificate: idCert,
    }
    const ctx: ProofContext = { theorems: new Map(), relations: new Map() }
    const direct = applyStep(s.d, step, ctx)
    const round = stepFromJson(JSON.parse(JSON.stringify(stepToJson(step))))
    const replayed = applyStep(s.d, round, ctx)
    const boundary = [outWireOf(direct, s.zb)]
    expect(boundaryFingerprint(mkDiagramWithBoundary(replayed, [outWireOf(replayed, s.zb)])))
      .toBe(boundaryFingerprint(mkDiagramWithBoundary(direct, boundary)))
  })
})
