import { describe, it, expect } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import {
  mkDiagram, DiagramError,
  type DiagramNode, type Wire,
} from '../../../src/kernel/diagram/diagram'
import { mkDiagramWithBoundary, type DiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { TERM, relSig, sigKey, type Sig } from '../../../src/kernel/diagram/sig'
import { RuleError } from '../../../src/kernel/rules/error'
import { applyBodyAttach, applyBodyDetach } from '../../../src/kernel/rules/body'
import { exploreForm } from '../../../src/kernel/diagram/canonical/explore'

/**
 * Build a content interface: arg stubs of `argSigs` followed by param stubs of
 * `paramSigs`, all root-scoped endpoint-free wires. Boundary order is stubs
 * then params, matching the body-node contract (spec §2.2).
 */
function mkContent(argSigs: readonly Sig[], paramSigs: readonly Sig[]): DiagramWithBoundary {
  const wires: Record<string, Wire> = {}
  const boundary: string[] = []
  argSigs.forEach((s, i) => {
    const id = `aw${i}`
    wires[id] = { scope: 'c0', sig: s, endpoints: [] }
    boundary.push(id)
  })
  paramSigs.forEach((s, j) => {
    const id = `pw${j}`
    wires[id] = { scope: 'c0', sig: s, endpoints: [] }
    boundary.push(id)
  })
  return mkDiagramWithBoundary(
    mkDiagram({ root: 'c0', regions: { c0: { kind: 'sheet' } }, wires }),
    boundary,
  )
}

/** Enumerate the body nodes of a diagram as [id, node] pairs. */
function bodyNodes(d: { nodes: Readonly<Record<string, DiagramNode>> }): [string, Extract<DiagramNode, { kind: 'body' }>][] {
  return Object.entries(d.nodes).filter(
    (e): e is [string, Extract<DiagramNode, { kind: 'body' }>] => e[1].kind === 'body',
  )
}

describe('body attach: signature gate', () => {
  it('refuses to attach a body to a TERM wire, naming the wire and its sig key', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const wT = h.wire(cut, [], TERM)
    const d = h.build()
    const content = mkContent([TERM], [])
    expect(() => applyBodyAttach(d, wT, content, []))
      .toThrowError(/wire '.*' sig 't' is not a relation signature/)
    expect(() => applyBodyAttach(d, wT, content, [])).toThrow(RuleError)
  })
})

describe('body attach: boundary arithmetic', () => {
  it('refuses when boundary length != sig arity + param count', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const wR = h.relWire(cut, relSig([TERM]))
    const d = h.build()
    // sig arity 1, params 0 -> expects boundary length 1; give 2.
    const content = mkContent([TERM, TERM], [])
    expect(() => applyBodyAttach(d, wR, content, []))
      .toThrowError(/2 boundary wires.*arity 1.*0 param/)
    expect(() => applyBodyAttach(d, wR, content, [])).toThrow(RuleError)
  })
})

describe('body attach: parameter gates', () => {
  it('refuses a parameter whose sig disagrees with the content boundary param sig', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const wR = h.relWire(cut, relSig([TERM]))
    const pW = h.wire(h.root, [], TERM) // param wire is t
    const d = h.build()
    // content declares its param stub as (t): mismatch with the t param wire.
    const content = mkContent([TERM], [relSig([TERM])])
    expect(() => applyBodyAttach(d, wR, content, [pW]))
      .toThrowError(/parameter wire '.*' sig 't' does not match content boundary parameter sig '\(t\)'/)
  })

  it('refuses a parameter wire scoped strictly inside the target wire scope', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const inner = h.cut(cut) // strictly inside the target scope
    const wR = h.relWire(cut, relSig([TERM]))
    const pW = h.wire(inner, [], TERM)
    const d = h.build()
    const content = mkContent([TERM], [TERM])
    expect(() => applyBodyAttach(d, wR, content, [pW]))
      .toThrowError(/parameter wire '.*' .*must be at or outside the target wire's scope/)
  })

  it('accepts a parameter wire scoped in the SAME region as the target wire (at-or-outside admits equality)', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root) // negative: forward attach ok
    const wR = h.relWire(cut, relSig([TERM]))
    const pW = h.wire(cut, [], TERM) // same region as the target wire
    const d = h.build()
    const content = mkContent([TERM], [TERM])
    expect(() => applyBodyAttach(d, wR, content, [pW])).not.toThrow()
  })
})

describe('body attach: polarity gate', () => {
  it('forward attach refuses a target wire at a POSITIVE scope', () => {
    const h = new DiagramBuilder()
    const wR = h.relWire(h.root, relSig([TERM])) // root is positive
    const d = h.build()
    const content = mkContent([TERM], [])
    expect(() => applyBodyAttach(d, wR, content, [], 'forward'))
      .toThrowError(/requires a negative.*positive/)
    expect(() => applyBodyAttach(d, wR, content, [], 'forward')).toThrow(RuleError)
  })

  it('backward attach refuses a target wire at a NEGATIVE scope', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root) // negative
    const wR = h.relWire(cut, relSig([TERM]))
    const d = h.build()
    const content = mkContent([TERM], [])
    expect(() => applyBodyAttach(d, wR, content, [], 'backward'))
      .toThrowError(/backward.*requires a positive.*negative/)
    expect(() => applyBodyAttach(d, wR, content, [], 'backward')).toThrow(RuleError)
  })
})

describe('body attach: single-body gate', () => {
  it('refuses a second body on a wire that already carries one', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const wR = h.relWire(cut, relSig([TERM]))
    const d = h.build()
    const content = mkContent([TERM], [])
    const d1 = applyBodyAttach(d, wR, content, [])
    expect(() => applyBodyAttach(d1, wR, mkContent([TERM], []), []))
      .toThrowError(/wire '.*' already carries a body/)
  })
})

describe('body attach: happy path', () => {
  it('attaches a body at a negative scope with a param, deriving sig from the wire', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const wR = h.relWire(cut, relSig([TERM]))
    const pW = h.wire(h.root, [], TERM)
    const d = h.build()
    const content = mkContent([TERM], [TERM])
    const out = applyBodyAttach(d, wR, content, [pW], 'forward')

    const bodies = bodyNodes(out)
    expect(bodies).toHaveLength(1)
    const [bid, body] = bodies[0]!
    // node payload: sig derived from the target wire (never passed by the caller)
    expect(sigKey(body.sig)).toBe(sigKey(relSig([TERM])))
    expect(body.region).toBe(d.wires[wR]!.scope)
    expect(body.content).toBe(content)

    // output endpoint added onto the target wire
    const outEps = out.wires[wR]!.endpoints.filter((ep) => ep.node === bid && ep.port.kind === 'output')
    expect(outEps).toHaveLength(1)

    // the single param lands on freeVar port p0 of the param wire
    const pEps = out.wires[pW]!.endpoints.filter(
      (ep) => ep.node === bid && ep.port.kind === 'freeVar' && ep.port.name === 'p0',
    )
    expect(pEps).toHaveLength(1)
  })

  it('fails loudly when the content arg stub sig disagrees with the wire arg sig (mkDiagram gate)', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const wR = h.relWire(cut, relSig([relSig([TERM])])) // arg 0 is (t)
    const d = h.build()
    // content arg stub is t: does not match the wire's (t) arg.
    const content = mkContent([TERM], [])
    expect(() => applyBodyAttach(d, wR, content, []))
      .toThrowError(DiagramError)
  })
})

describe('body detach', () => {
  it('refuses a non-body node', () => {
    const h = new DiagramBuilder()
    const t = h.termNode(h.root, { kind: 'port', name: 'x' })
    const d = h.build()
    expect(() => applyBodyDetach(d, t))
      .toThrowError(/applies to body nodes/)
    expect(() => applyBodyDetach(d, t)).toThrow(RuleError)
  })

  it('forward detach refuses a body at a NEGATIVE scope', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const wR = h.relWire(cut, relSig([TERM]))
    const d1 = applyBodyAttach(h.build(), wR, mkContent([TERM], []), [], 'forward')
    const [bid] = bodyNodes(d1)[0]!
    expect(() => applyBodyDetach(d1, bid, 'forward'))
      .toThrowError(/requires a positive.*negative/)
  })

  it('backward detach refuses a body at a POSITIVE scope', () => {
    const h = new DiagramBuilder()
    const wR = h.relWire(h.root, relSig([TERM])) // positive
    const d1 = applyBodyAttach(h.build(), wR, mkContent([TERM], []), [], 'backward')
    const [bid] = bodyNodes(d1)[0]!
    expect(() => applyBodyDetach(d1, bid, 'backward'))
      .toThrowError(/backward.*requires a negative.*positive/)
  })

  it('forward attach then backward detach restores the original canonical form', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const wR = h.relWire(cut, relSig([TERM]))
    const pW = h.wire(h.root, [], TERM)
    const d0 = h.build()
    const d1 = applyBodyAttach(d0, wR, mkContent([TERM], [TERM]), [pW], 'forward')
    const [bid] = bodyNodes(d1)[0]!
    const d2 = applyBodyDetach(d1, bid, 'backward')
    expect(exploreForm(d2)).toBe(exploreForm(d0))
  })

  it('backward attach then forward detach restores the original canonical form', () => {
    const h = new DiagramBuilder()
    const wR = h.relWire(h.root, relSig([TERM])) // positive
    const pW = h.wire(h.root, [], TERM)
    const d0 = h.build()
    const d1 = applyBodyAttach(d0, wR, mkContent([TERM], [TERM]), [pW], 'backward')
    const [bid] = bodyNodes(d1)[0]!
    const d2 = applyBodyDetach(d1, bid, 'forward')
    expect(exploreForm(d2)).toBe(exploreForm(d0))
  })
})
