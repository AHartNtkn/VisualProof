import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { DiagramError, type Diagram, type NodeId } from '../../../src/kernel/diagram/diagram'
import type { Term } from '../../../src/kernel/term/term'
import { exploreForm } from '../../../src/kernel/diagram/canonical/explore'
import { applyConversion, applyConversionByCertificate } from '../../../src/kernel/rules/conversion'
import { proposePortCorrespondence, type PortCorrespondence } from '../../../src/kernel/rules/port-correspondence'

const p = (s: string) => parseTerm(s)
const correspondenceFor = (d: Diagram, node: NodeId, target: Term): PortCorrespondence => {
  const source = d.nodes[node]
  if (source === undefined || source.kind !== 'term') throw new Error('test setup requires a term node')
  return proposePortCorrespondence(source.term, target)
}

describe('applyConversion', () => {
  it('uses the witness-selected replacement interface, preserving an unused declared column', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('used'), ['used', 'unused'])
    const usedWire = h.wire(h.root, [{ node: n, port: { kind: 'freeVar', name: 'used' } }])
    const unusedWire = h.wire(h.root, [{ node: n, port: { kind: 'freeVar', name: 'unused' } }])
    const d = h.build()
    const correspondence: PortCorrespondence = {
      commonArity: 2,
      left: { s0: 0, s1: 1 },
      right: { renamed: 0, spare: 1 },
    }
    const out = applyConversion(d, n, p('renamed'), correspondence, 10).diagram
    const node = out.nodes[n]
    expect(node?.kind).toBe('term')
    if (node?.kind !== 'term') throw new Error('test setup requires a term node')
    expect(node.freePorts).toEqual(['s0', 's1'])
    expect(out.wires[usedWire]!.endpoints).toContainEqual({ node: n, port: { kind: 'freeVar', name: 's0' } })
    expect(out.wires[unusedWire]!.endpoints).toContainEqual({ node: n, port: { kind: 'freeVar', name: 's1' } })
  })

  it('applies prototype-named correspondence and attachment keys as ordinary own properties', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('\\x. x'))
    const attachment = h.wire(h.root, [])
    const d = h.build()
    const right = Object.fromEntries([['__proto__', 0]])
    const attachments = Object.fromEntries([['__proto__', attachment]])
    const target = p('(\\u. \\x. x) __proto__')
    const out = applyConversion(
      d,
      n,
      target,
      { commonArity: 1, left: {}, right },
      10,
      attachments,
    ).diagram
    const node = out.nodes[n]
    expect(node?.kind === 'term' && node.freePorts).toEqual(['s0'])
    expect(out.wires[attachment]!.endpoints)
      .toContainEqual({ node: n, port: { kind: 'freeVar', name: 's0' } })
  })

  it('accepts pure free-port renaming through a supplied common carrier and preserves the shared wire', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('x'))
    const original = h.wire(h.root, [{ node: n, port: { kind: 'freeVar', name: 'x' } }])
    const d = h.build()
    const correspondence: PortCorrespondence = {
      commonArity: 1,
      left: { s0: 0 },
      right: { renamed: 0 },
    }
    const { diagram, certificate } = applyConversion(d, n, p('renamed'), correspondence, 10)
    expect(diagram.wires[original]!.endpoints).toContainEqual({ node: n, port: { kind: 'freeVar', name: 's0' } })
    expect(applyConversionByCertificate(d, n, p('renamed'), certificate, correspondence).wires[original])
      .toBeDefined()
  })

  it('detaches left-only columns and permits right-only attachment through the common carrier', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('(\\u. kept) erased'))
    const hub = h.termNode(h.root, p('\\x. x'))
    const erasedWire = h.wire(h.root, [{ node: n, port: { kind: 'freeVar', name: 'erased' } }])
    const attachment = h.wire(h.root, [{ node: hub, port: { kind: 'output' } }])
    const d = h.build()
    const correspondence: PortCorrespondence = {
      commonArity: 3,
      left: { s0: 0, s1: 1 },
      right: { renamed: 0, added: 2 },
    }
    const result = applyConversion(d, n, p('(\\u. renamed) added'), correspondence, 10, { added: attachment })
    expect(result.diagram.wires[erasedWire]!.endpoints).toHaveLength(0)
    expect(result.diagram.wires[attachment]!.endpoints).toContainEqual({
      node: n,
      port: { kind: 'freeVar', name: 's1' },
    })
  })

  it('rejects a correspondence whose exact keys do not cover the converted terms', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('x'))
    const d = h.build()
    expect(() => applyConversion(d, n, p('renamed'), {
      commonArity: 1,
      left: { stale: 0 },
      right: { renamed: 0 },
    }, 10)).toThrowError(/left keys/)
  })

  it('normalizes a node term in place (same ports), returning a certificate', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('(\\x. x) y'))
    const d = h.build()
    // the node's source free 'y' is canonical s0 after construction; the
    // conversion target must be spelled in the node's CURRENT port names
    const target = p('s0')
    const { diagram, certificate } = applyConversion(d, n, target, correspondenceFor(d, n, target), 10)
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
    const target = p('s0')
    const { diagram } = applyConversion(d, n, target, correspondenceFor(d, n, target), 10)
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
    const target = p('(\\x. s0) z')
    const correspondence = correspondenceFor(d, n, target)
    const named = applyConversion(d, n, target, correspondence, 10, { z: wz }).diagram
    expect(named.wires[wz]?.endpoints).toHaveLength(2)
    const fresh = applyConversion(d, n, target, correspondence, 10).diagram
    const newWires = Object.keys(fresh.wires).filter((id) => d.wires[id] === undefined)
    expect(newWires).toHaveLength(1)
    expect(fresh.wires[newWires[0]!]?.scope).toBe(d.root)
    expect(fresh.wires[newWires[0]!]?.endpoints).toHaveLength(1)
  })

  it('conversion round-trips by fingerprint when the port sets match', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('(\\x. x) y'))
    const d = h.build()
    const thereTarget = p('s0')
    const there = applyConversion(d, n, thereTarget, correspondenceFor(d, n, thereTarget), 10).diagram
    const backTarget = p('(\\x. x) s0')
    const back = applyConversion(there, n, backTarget, correspondenceFor(there, n, backTarget), 10).diagram
    expect(exploreForm(back)).toBe(exploreForm(d))
  })

  it('rejects non-convertible terms by name', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('\\x. x'))
    const d = h.build()
    const target = p('\\x. \\y. x')
    expect(() => applyConversion(d, n, target, correspondenceFor(d, n, target), 10))
      .toThrowError(/not βη-convertible/)
  })

  it('reports fuel exhaustion by name', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('(\\x. x x) (\\x. x x)'))
    const d = h.build()
    const target = p('\\x. x')
    expect(() => applyConversion(d, n, target, correspondenceFor(d, n, target), 5))
      .toThrowError(/undecided under fuel 5/)
  })

  it('rejects atoms and unknown nodes with the right vocabulary', () => {
    const h = new DiagramBuilder()
    const bub = h.bubble(h.root, 0)
    const a = h.atom(bub, bub)
    const d = h.build()
    const correspondence = { commonArity: 1, left: {}, right: { y: 0 } }
    expect(() => applyConversion(d, a, p('y'), correspondence, 10)).toThrowError(/term nodes/)
    let caught: unknown
    try { applyConversion(d, 'ghost', p('y'), correspondence, 10) } catch (e) { caught = e }
    expect(caught).toBeInstanceOf(DiagramError)
  })

  it('rejects attachments naming ports that are not newly added', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('(\\x. x) y'))
    const d = h.build()
    let caught: unknown
    // s0 survives the conversion (it is not newly added), so attaching it is invalid
    const target = p('s0')
    try { applyConversion(d, n, target, correspondenceFor(d, n, target), 10, { s0: 'w0' }) } catch (e) { caught = e }
    expect(caught).toBeInstanceOf(DiagramError)
  })

  it('works inside nested regions: fresh wires at the node region, not root', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const inner = h.cut(cut)
    const n = h.termNode(inner, p('y'))
    const d = h.build()
    const target = p('(\\x. s0) z')
    const out = applyConversion(d, n, target, correspondenceFor(d, n, target), 10).diagram
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
    const target = p('s0')
    const correspondence = correspondenceFor(d, n, target)
    const { certificate } = applyConversion(d, n, target, correspondence, 10)
    const replayed = applyConversionByCertificate(d, n, target, certificate, correspondence)
    expect(replayed.nodes[n]?.kind).toBe('term')
    const forged: import('../../../src/kernel/term/certificate').ConversionCertificate = { leftSteps: [], rightSteps: [] }
    expect(() => applyConversionByCertificate(d, n, target, forged, correspondence))
      .toThrowError(/certificate rejected/)
  })
})
