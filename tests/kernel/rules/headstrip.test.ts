import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import type { Term } from '../../../src/kernel/term/term'
import { app, bvar, lam, port, termEq } from '../../../src/kernel/term/term'
import type { Diagram, Endpoint, NodeId, WireId } from '../../../src/kernel/diagram/diagram'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { applyHeadStrip } from '../../../src/kernel/rules/headstrip'
import { RuleError } from '../../../src/kernel/rules/error'

const p = (s: string) => parseTerm(s)

const fv = (node: NodeId, name: string): Endpoint => ({ node, port: { kind: 'freeVar', name } })
const outp = (node: NodeId): Endpoint => ({ node, port: { kind: 'output' } })

const addedNodes = (before: Diagram, after: Diagram): NodeId[] =>
  Object.keys(after.nodes).filter((id) => before.nodes[id] === undefined)

const termOf = (d: Diagram, id: NodeId): Term => {
  const n = d.nodes[id]
  if (n === undefined || n.kind !== 'term') throw new Error(`test expected term node '${id}'`)
  return n.term
}

/** The unique wire holding the node's output port (port identified by KIND only, never name). */
const outputWire = (d: Diagram, node: NodeId): WireId => {
  const hit = Object.entries(d.wires).find(([, w]) =>
    w.endpoints.some((ep) => ep.node === node && ep.port.kind === 'output'))
  if (hit === undefined) throw new Error(`test: no output wire for '${node}'`)
  return hit[0]
}

/** All wires holding any freeVar port of the node (identified by KIND only, never name). */
const freeVarWires = (d: Diagram, node: NodeId): WireId[] =>
  Object.entries(d.wires)
    .filter(([, w]) => w.endpoints.some((ep) => ep.node === node && ep.port.kind === 'freeVar'))
    .map(([id]) => id)

describe('head strip (rigid-head equation decomposition)', () => {
  it('strips \\x. x a b —o— \\x. x a c into ONE added equation pair', () => {
    const h = new DiagramBuilder()
    const n1 = h.termNode(h.root, p('\\x. x a b'))
    const n2 = h.termNode(h.root, p('\\x. x a c'))
    const wa = h.wire(h.root, [fv(n1, 'a'), fv(n2, 'a')])
    const wb = h.wire(h.root, [fv(n1, 'b')])
    const wc = h.wire(h.root, [fv(n2, 'c')])
    const weq = h.wire(h.root, [outp(n1), outp(n2)])
    const d = h.build()
    const out = applyHeadStrip(d, n1, n2)
    const added = addedNodes(d, out)
    expect(added).toHaveLength(2)
    // every single-free closure is canonically the term 's0'; the b- and
    // c-copies are distinguished by WIRING (which parent wire they ride)
    const bNode = added.find((id) => freeVarWires(out, id).includes(wb))
    const cNode = added.find((id) => freeVarWires(out, id).includes(wc))
    expect(bNode).toBeDefined()
    expect(cNode).toBeDefined()
    expect(bNode).not.toBe(cNode)
    expect(termEq(termOf(out, bNode!), p('\\x. s0'))).toBe(true)
    expect(termEq(termOf(out, cNode!), p('\\x. s0'))).toBe(true)
    expect(out.nodes[bNode!]!.region).toBe(h.root)
    expect(out.nodes[cNode!]!.region).toBe(h.root)
    // closure free ports ride exactly the wires those ports ride on the parents
    expect(freeVarWires(out, bNode!)).toEqual([wb])
    expect(freeVarWires(out, cNode!)).toEqual([wc])
    // the two added outputs share ONE fresh wire scoped at the region
    const wo = outputWire(out, bNode!)
    expect(outputWire(out, cNode!)).toBe(wo)
    expect(d.wires[wo]).toBeUndefined()
    expect(out.wires[wo]!.scope).toBe(h.root)
    expect(out.wires[wo]!.endpoints).toHaveLength(2)
    // originals untouched (both parents canonicalize to the SAME spelling —
    // their distinction lives entirely in the wiring)
    expect(termEq(termOf(out, n1), p('\\x. x s0 s1'))).toBe(true)
    expect(termEq(termOf(out, n2), p('\\x. x s0 s1'))).toBe(true)
    expect(outputWire(out, n1)).toBe(weq)
    expect(outputWire(out, n2)).toBe(weq)
    expect(out.wires[weq]!.endpoints).toHaveLength(2)
    // the skipped position gained no endpoints
    expect(out.wires[wa]!.endpoints).toHaveLength(2)
  })

  it('does NOT skip a termEq position whose free port rides different wires', () => {
    const h = new DiagramBuilder()
    const n1 = h.termNode(h.root, p('\\x. x a b'))
    const n2 = h.termNode(h.root, p('\\x. x a c'))
    const wa1 = h.wire(h.root, [fv(n1, 'a')])
    const wa2 = h.wire(h.root, [fv(n2, 'a')])
    h.wire(h.root, [fv(n1, 'b')])
    h.wire(h.root, [fv(n2, 'c')])
    h.wire(h.root, [outp(n1), outp(n2)])
    const d = h.build()
    const out = applyHeadStrip(d, n1, n2)
    const added = addedNodes(d, out)
    // both positions strip: two equation pairs
    expect(added).toHaveLength(4)
    // all four closures are canonically the single-port term 's0'; the two
    // a-copies are the ones riding the parents' a-wires
    const aNodes = added.filter((id) => {
      const ws = freeVarWires(out, id)
      return ws.length === 1 && (ws[0] === wa1 || ws[0] === wa2)
    })
    expect(aNodes).toHaveLength(2)
    for (const id of aNodes) expect(termEq(termOf(out, id), p('\\x. s0'))).toBe(true)
    // one copy hangs off each parent's a-wire, and they share an output wire
    const ridden = aNodes.flatMap((id) => freeVarWires(out, id))
    expect(new Set(ridden)).toEqual(new Set([wa1, wa2]))
    const [a1, a2] = aNodes
    expect(outputWire(out, a1!)).toBe(outputWire(out, a2!))
  })

  it('is polarity-blind: works identically inside a cut, fresh wire scoped there', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const n1 = h.termNode(cut, p('\\x. x a b'))
    const n2 = h.termNode(cut, p('\\x. x a c'))
    h.wire(cut, [fv(n1, 'a'), fv(n2, 'a')])
    h.wire(cut, [fv(n1, 'b')])
    h.wire(cut, [fv(n2, 'c')])
    h.wire(cut, [outp(n1), outp(n2)])
    const d = h.build()
    const out = applyHeadStrip(d, n1, n2)
    const added = addedNodes(d, out)
    expect(added).toHaveLength(2)
    for (const id of added) expect(out.nodes[id]!.region).toBe(cut)
    const wo = outputWire(out, added[0]!)
    expect(outputWire(out, added[1]!)).toBe(wo)
    expect(out.wires[wo]!.scope).toBe(cut)
  })

  it('strips under the binder: \\x. x a —o— \\x. x b yields closures \\x. a and \\x. b', () => {
    const h = new DiagramBuilder()
    const n1 = h.termNode(h.root, p('\\x. x a'))
    const n2 = h.termNode(h.root, p('\\x. x b'))
    const wa = h.wire(h.root, [fv(n1, 'a')])
    const wb = h.wire(h.root, [fv(n2, 'b')])
    h.wire(h.root, [outp(n1), outp(n2)])
    const d = h.build()
    const out = applyHeadStrip(d, n1, n2)
    const added = addedNodes(d, out)
    expect(added).toHaveLength(2)
    // both closures are canonically \x. s0 — distinguished by wiring alone
    const ca = added.find((id) => freeVarWires(out, id).includes(wa))
    const cb = added.find((id) => freeVarWires(out, id).includes(wb))
    expect(ca).toBeDefined()
    expect(cb).toBeDefined()
    expect(ca).not.toBe(cb)
    expect(termEq(termOf(out, ca!), p('\\x. s0'))).toBe(true)
    expect(termEq(termOf(out, cb!), p('\\x. s0'))).toBe(true)
    expect(freeVarWires(out, ca!)).toEqual([wa])
    expect(freeVarWires(out, cb!)).toEqual([wb])
    expect(outputWire(out, ca!)).toBe(outputWire(out, cb!))
  })

  it('builds prefix-closures with unshifted indices: an arg referencing an outer prefix binder survives wrapping', () => {
    const h = new DiagramBuilder()
    const n1 = h.termNode(h.root, p('\\x. \\y. y (x a)'))
    const n2 = h.termNode(h.root, p('\\x. \\y. y (x b)'))
    const wa = h.wire(h.root, [fv(n1, 'a')])
    const wb = h.wire(h.root, [fv(n2, 'b')])
    h.wire(h.root, [outp(n1), outp(n2)])
    const d = h.build()
    const out = applyHeadStrip(d, n1, n2)
    const added = addedNodes(d, out)
    expect(added).toHaveLength(2)
    // Directly-constructed expected closure: \x. \y. x s0 — the arg's bvar 1
    // (the OUTER prefix binder) must be wrapped UNCHANGED; a shift in either
    // direction would equate the wrong functions. The single free is
    // canonically s0 on both copies, so they are distinguished by wiring.
    const exp = lam(lam(app(bvar(1), port('s0'))))
    const ca = added.find((id) => freeVarWires(out, id).includes(wa))
    const cb = added.find((id) => freeVarWires(out, id).includes(wb))
    expect(ca).toBeDefined()
    expect(cb).toBeDefined()
    expect(ca).not.toBe(cb)
    expect(termEq(termOf(out, ca!), exp)).toBe(true)
    expect(termEq(termOf(out, cb!), exp)).toBe(true)
    expect(freeVarWires(out, ca!)).toEqual([wa])
    expect(freeVarWires(out, cb!)).toEqual([wb])
    expect(outputWire(out, ca!)).toBe(outputWire(out, cb!))
  })

  it('scopes the fresh equation wire at the nodes region inside a nested cut (cut within a cut)', () => {
    const h = new DiagramBuilder()
    const outer = h.cut(h.root)
    const inner = h.cut(outer)
    const n1 = h.termNode(inner, p('\\x. x a'))
    const n2 = h.termNode(inner, p('\\x. x b'))
    h.wire(inner, [fv(n1, 'a')])
    h.wire(inner, [fv(n2, 'b')])
    h.wire(inner, [outp(n1), outp(n2)])
    const d = h.build()
    const out = applyHeadStrip(d, n1, n2)
    const added = addedNodes(d, out)
    expect(added).toHaveLength(2)
    for (const id of added) expect(out.nodes[id]!.region).toBe(inner)
    const wo = outputWire(out, added[0]!)
    expect(outputWire(out, added[1]!)).toBe(wo)
    expect(out.wires[wo]!.scope).toBe(inner)
  })

  it('is a no-op when every position is trivial (nothing added, nothing removed)', () => {
    const h = new DiagramBuilder()
    const n1 = h.termNode(h.root, p('\\x. x a'))
    const n2 = h.termNode(h.root, p('\\x. x a'))
    h.wire(h.root, [fv(n1, 'a'), fv(n2, 'a')])
    h.wire(h.root, [outp(n1), outp(n2)])
    const d = h.build()
    const out = applyHeadStrip(d, n1, n2)
    expect(addedNodes(d, out)).toHaveLength(0)
    expect(Object.keys(out.wires).sort()).toEqual(Object.keys(d.wires).sort())
  })

  it('refuses the same node twice', () => {
    const h = new DiagramBuilder()
    const n1 = h.termNode(h.root, p('f a'))
    h.wire(h.root, [outp(n1)])
    const d = h.build()
    expect(() => applyHeadStrip(d, n1, n1)).toThrowError(/distinct/)
  })

  it('refuses nodes in different regions', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const n1 = h.termNode(h.root, p('f a'))
    const n2 = h.termNode(cut, p('f a'))
    h.wire(h.root, [fv(n1, 'f'), fv(n2, 'f')])
    h.wire(h.root, [fv(n1, 'a'), fv(n2, 'a')])
    h.wire(h.root, [outp(n1), outp(n2)])
    expect(() => applyHeadStrip(h.build(), n1, n2)).toThrowError(/one region/)
  })

  it('refuses outputs on different wires (no equation between the nodes)', () => {
    const h = new DiagramBuilder()
    const n1 = h.termNode(h.root, p('f a b'))
    const n2 = h.termNode(h.root, p('f a c'))
    h.wire(h.root, [fv(n1, 'f'), fv(n2, 'f')])
    h.wire(h.root, [fv(n1, 'a'), fv(n2, 'a')])
    h.wire(h.root, [outp(n1)])
    h.wire(h.root, [outp(n2)])
    expect(() => applyHeadStrip(h.build(), n1, n2)).toThrowError(/one wire/)
  })

  it('refuses a redex head, pointing to the HNF tactic', () => {
    const h = new DiagramBuilder()
    const n1 = h.termNode(h.root, p('(\\u. u) a'))
    const n2 = h.termNode(h.root, p('(\\u. u) a'))
    h.wire(h.root, [fv(n1, 'a'), fv(n2, 'a')])
    h.wire(h.root, [outp(n1), outp(n2)])
    expect(() => applyHeadStrip(h.build(), n1, n2)).toThrowError(/HNF tactic/)
  })

  it('refuses unequal binder counts, with the counts in the message', () => {
    const h = new DiagramBuilder()
    const n1 = h.termNode(h.root, p('\\x. f x'))
    const n2 = h.termNode(h.root, p('f a'))
    h.wire(h.root, [fv(n1, 'f'), fv(n2, 'f')])
    h.wire(h.root, [fv(n2, 'a')])
    h.wire(h.root, [outp(n1), outp(n2)])
    expect(() => applyHeadStrip(h.build(), n1, n2)).toThrowError(/binder counts differ: 1 vs 0/)
  })

  it('refuses unequal argument counts, with the counts in the message', () => {
    const h = new DiagramBuilder()
    const n1 = h.termNode(h.root, p('f a b'))
    const n2 = h.termNode(h.root, p('f a'))
    h.wire(h.root, [fv(n1, 'f'), fv(n2, 'f')])
    h.wire(h.root, [fv(n1, 'a'), fv(n2, 'a')])
    h.wire(h.root, [fv(n1, 'b')])
    h.wire(h.root, [outp(n1), outp(n2)])
    expect(() => applyHeadStrip(h.build(), n1, n2)).toThrowError(/argument counts differ: 2 vs 1/)
  })

  it('refuses free heads even when their names and wires correspond', () => {
    const h = new DiagramBuilder()
    const n1 = h.termNode(h.root, p('f a'))
    const n2 = h.termNode(h.root, p('f a'))
    h.wire(h.root, [fv(n1, 'f'), fv(n2, 'f')])
    h.wire(h.root, [fv(n1, 'a'), fv(n2, 'a')])
    h.wire(h.root, [outp(n1), outp(n2)])
    expect(() => applyHeadStrip(h.build(), n1, n2)).toThrowError(/bound rigid heads/)
  })

  it('refuses a bound head against a free head', () => {
    const h = new DiagramBuilder()
    const n1 = h.termNode(h.root, p('\\x. x a'))
    const n2 = h.termNode(h.root, p('\\x. f a'))
    h.wire(h.root, [fv(n1, 'a'), fv(n2, 'a')])
    h.wire(h.root, [fv(n2, 'f')])
    h.wire(h.root, [outp(n1), outp(n2)])
    expect(() => applyHeadStrip(h.build(), n1, n2)).toThrowError(/bound rigid heads/)
  })

  it('refuses bound heads with different indices', () => {
    const h = new DiagramBuilder()
    const n1 = h.termNode(h.root, p('\\x. \\y. x a'))
    const n2 = h.termNode(h.root, p('\\x. \\y. y a'))
    h.wire(h.root, [fv(n1, 'a'), fv(n2, 'a')])
    h.wire(h.root, [outp(n1), outp(n2)])
    expect(() => applyHeadStrip(h.build(), n1, n2)).toThrowError(/bound indices differ/)
  })

  it('throws RuleError (gate vocabulary) for gate refusals', () => {
    const h = new DiagramBuilder()
    const n1 = h.termNode(h.root, p('f a b'))
    const n2 = h.termNode(h.root, p('f a c'))
    h.wire(h.root, [outp(n1)])
    h.wire(h.root, [outp(n2)])
    expect(() => applyHeadStrip(h.build(), n1, n2)).toThrowError(RuleError)
  })
})
