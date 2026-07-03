import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { DiagramError } from '../../../src/kernel/diagram/diagram'
import { exploreForm } from '../../../src/kernel/diagram/canonical/explore'
import { applyConversion, applyConversionByCertificate } from '../../../src/kernel/rules/conversion'

const p = (s: string) => parseTerm(s)

describe('applyConversion', () => {
  it('normalizes a node term in place (same ports), returning a certificate', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('(\\x. x) y'))
    const d = h.build()
    // the node's source free 'y' is canonical s0 after construction; the
    // conversion target must be spelled in the node's CURRENT port names
    const { diagram, certificate } = applyConversion(d, n, p('s0'), 10)
    expect(diagram.nodes[n]?.kind).toBe('term')
    expect(certificate.leftSteps.length).toBeGreaterThan(0)
    // ports unchanged: y's wire still has its endpoint
    const after = Object.values(diagram.wires).filter((w) => w.endpoints.some((ep) => ep.node === n))
    expect(after).toHaveLength(2) // output + y
  })

  it('detaches vanished ports, trimming their wires', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('(\\x. y) z'))
    const hub = h.termNode(h.root, p('\\x. x'))
    const wz = h.wire(h.root, [
      { node: n, port: { kind: 'freeVar', name: 'z' } },
      { node: hub, port: { kind: 'output' } },
    ])
    const d = h.build()
    // node frees canonicalized y->s0, z->s1; converting to s0 drops s1 (source 'z')
    const { diagram } = applyConversion(d, n, p('s0'), 10)
    expect(diagram.wires[wz]?.endpoints).toHaveLength(1)
    expect(diagram.wires[wz]?.endpoints[0]?.node).toBe(hub)
  })

  it('attaches added ports to named wires, or to fresh singletons', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('y'))
    const hub = h.termNode(h.root, p('\\x. x'))
    const wz = h.wire(h.root, [{ node: hub, port: { kind: 'output' } }])
    const d = h.build()
    // node 'y' is canonical s0; the target must reduce to s0 and adds port z
    const named = applyConversion(d, n, p('(\\x. s0) z'), 10, { z: wz }).diagram
    expect(named.wires[wz]?.endpoints).toHaveLength(2)
    const fresh = applyConversion(d, n, p('(\\x. s0) z'), 10).diagram
    const newWires = Object.keys(fresh.wires).filter((id) => d.wires[id] === undefined)
    expect(newWires).toHaveLength(1)
    expect(fresh.wires[newWires[0]!]?.scope).toBe(d.root)
    expect(fresh.wires[newWires[0]!]?.endpoints).toHaveLength(1)
  })

  it('conversion round-trips by fingerprint when the port sets match', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('(\\x. x) y'))
    const d = h.build()
    const there = applyConversion(d, n, p('s0'), 10).diagram
    const back = applyConversion(there, n, p('(\\x. x) s0'), 10).diagram
    expect(exploreForm(back)).toBe(exploreForm(d))
  })

  it('rejects non-convertible terms by name', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('\\x. x'))
    const d = h.build()
    expect(() => applyConversion(d, n, p('\\x. \\y. x'), 10))
      .toThrowError(/not βη-convertible/)
  })

  it('reports fuel exhaustion by name', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('(\\x. x x) (\\x. x x)'))
    const d = h.build()
    expect(() => applyConversion(d, n, p('\\x. x'), 5))
      .toThrowError(/undecided under fuel 5/)
  })

  it('rejects atoms and unknown nodes with the right vocabulary', () => {
    const h = new DiagramBuilder()
    const bub = h.bubble(h.root, 0)
    const a = h.atom(bub, bub)
    const d = h.build()
    expect(() => applyConversion(d, a, p('y'), 10)).toThrowError(/term nodes/)
    let caught: unknown
    try { applyConversion(d, 'ghost', p('y'), 10) } catch (e) { caught = e }
    expect(caught).toBeInstanceOf(DiagramError)
  })

  it('rejects attachments naming ports that are not newly added', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('(\\x. x) y'))
    const d = h.build()
    let caught: unknown
    // s0 survives the conversion (it is not newly added), so attaching it is invalid
    try { applyConversion(d, n, p('s0'), 10, { s0: 'w0' }) } catch (e) { caught = e }
    expect(caught).toBeInstanceOf(DiagramError)
  })

  it('works inside nested regions: fresh wires at the node region, not root', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const inner = h.cut(cut)
    const n = h.termNode(inner, p('y'))
    const d = h.build()
    const out = applyConversion(d, n, p('(\\x. s0) z'), 10).diagram
    const newWires = Object.keys(out.wires).filter((id) => d.wires[id] === undefined)
    expect(newWires).toHaveLength(1)
    expect(out.wires[newWires[0]!]?.scope).toBe(inner)
  })
})

describe('applyConversionByCertificate', () => {
  it('replays a stored certificate without fuel and rejects forged ones by name', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('(\\x. x) y'))
    const d = h.build()
    const { certificate } = applyConversion(d, n, p('s0'), 10)
    const replayed = applyConversionByCertificate(d, n, p('s0'), certificate)
    expect(replayed.nodes[n]?.kind).toBe('term')
    const forged: import('../../../src/kernel/term/certificate').ConversionCertificate = { leftSteps: [], rightSteps: [] }
    expect(() => applyConversionByCertificate(d, n, p('s0'), forged))
      .toThrowError(/certificate rejected/)
  })
})
