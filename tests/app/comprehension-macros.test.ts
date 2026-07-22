import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import type { Diagram, RegionId, WireId } from '../../src/kernel/diagram/diagram'
import { mkDiagramWithBoundary, type DiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { relSig, TERM, type RelSig } from '../../src/kernel/diagram/sig'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { exploreForm } from '../../src/kernel/diagram/canonical/explore'
import { RuleError } from '../../src/kernel/rules/error'
import { applyBodyAttach, applyBodyDetach } from '../../src/kernel/rules/body'
import { applyUnfold } from '../../src/kernel/rules/fold'
import { applyVacuousElim } from '../../src/kernel/rules/vacuous'
import {
  macroComprehensionInstantiate,
  macroComprehensionAbstract,
} from '../../src/app/interact/comprehension-macros'

/**
 * Conservativity replay: every scenario of the retired monolithic
 * `applyComprehensionInstantiate` / `applyComprehensionAbstract` rebuilt against
 * the signature-indexed wire model and driven through the macro composites.
 * The old tests' bubbles/atom-binders become relational wires + bodied atoms;
 * region dissolution becomes body-detach + vacuous-elim; the old canonical-form
 * expectations become hand-built new-model diagrams compared under exploreForm.
 */

const p = (s: string) => parseTerm(s)
const R1: RelSig = relSig([TERM])
const R2: RelSig = relSig([TERM, TERM])

/* -------------------------------------------------------------------------- */
/* Comprehension bodies (args-then-params boundary order).                     */
/* -------------------------------------------------------------------------- */

/** Arity 1, no params: "the argument is the identity function" (λx.x on the arg stub). */
function identityComp(): DiagramWithBoundary {
  const b = new DiagramBuilder()
  const n = b.termNode(b.root, p('\\x. x'))
  const w0 = b.wire(b.root, [{ node: n, port: { kind: 'output' } }], TERM)
  return mkDiagramWithBoundary(b.build(), [w0])
}

/** Arity 2, no params: arg0 = output of λx.x, arg1 = a bare stub (for the R(x,x) diagonal). */
function arity2IdentComp(): DiagramWithBoundary {
  const b = new DiagramBuilder()
  const n = b.termNode(b.root, p('\\x. x'))
  const w0 = b.wire(b.root, [{ node: n, port: { kind: 'output' } }], TERM)
  const w1 = b.wire(b.root, [], TERM)
  return mkDiagramWithBoundary(b.build(), [w0, w1])
}

/** Arity 1, one TERM param: R(x) := "x —o— q", q on the parameter stub. Boundary [stub x, param q]. */
function paramComp(): DiagramWithBoundary {
  const b = new DiagramBuilder()
  const n = b.termNode(b.root, p('q'))
  const wx = b.wire(b.root, [{ node: n, port: { kind: 'output' } }], TERM)
  const wq = b.wire(b.root, [{ node: n, port: { kind: 'freeVar', name: 'q' } }], TERM)
  return mkDiagramWithBoundary(b.build(), [wx, wq])
}

/** Arity 1, one RELATION param: inner atom S(x) — arg on the arg stub, head on the param stub. */
function relParamComp(): DiagramWithBoundary {
  const b = new DiagramBuilder()
  const inner = b.atom(b.root, R1)
  const arg = b.wire(b.root, [{ node: inner, port: { kind: 'arg', index: 0 } }], TERM)
  const param = b.wire(b.root, [{ node: inner, port: { kind: 'head' } }], R1)
  return mkDiagramWithBoundary(b.build(), [arg, param])
}

/** Binary comp G(a,b): node `y`, output on b0, free var y on b1. */
function binaryComp(): DiagramWithBoundary {
  const b = new DiagramBuilder()
  const bn = b.termNode(b.root, p('y'))
  const b0 = b.wire(b.root, [{ node: bn, port: { kind: 'output' } }], TERM)
  const b1 = b.wire(b.root, [{ node: bn, port: { kind: 'freeVar', name: 'y' } }], TERM)
  return mkDiagramWithBoundary(b.build(), [b0, b1])
}

/** Ternary comp G(a,b,c): node `f g`, output b0, free var f b1, free var g b2. */
function ternaryComp(): DiagramWithBoundary {
  const b = new DiagramBuilder()
  const bn = b.termNode(b.root, p('f g'))
  const b0 = b.wire(b.root, [{ node: bn, port: { kind: 'output' } }], TERM)
  const b1 = b.wire(b.root, [{ node: bn, port: { kind: 'freeVar', name: 'f' } }], TERM)
  const b2 = b.wire(b.root, [{ node: bn, port: { kind: 'freeVar', name: 'g' } }], TERM)
  return mkDiagramWithBoundary(b.build(), [b0, b1, b2])
}

/* -------------------------------------------------------------------------- */
/* Small helpers.                                                              */
/* -------------------------------------------------------------------------- */

/** Nest `depth` cuts under root; return the innermost region. */
function nest(b: DiagramBuilder, depth: number): RegionId {
  let region = b.root
  for (let i = 0; i < depth; i++) region = b.cut(region)
  return region
}

const termNodes = (d: Diagram) => Object.values(d.nodes).filter((n) => n.kind === 'term')
const atomNodes = (d: Diagram) => Object.values(d.nodes).filter((n) => n.kind === 'atom')
const relWires = (d: Diagram) => Object.entries(d.wires).filter(([, w]) => w.sig.kind === 'rel')

/* ========================================================================== */
/* INSTANTIATION                                                              */
/* ========================================================================== */

describe('macroComprehensionInstantiate — core (replay of applyComprehensionInstantiate)', () => {
  it('replaces the sole atom by the comprehension copy and dissolves the ∃R wire', () => {
    // ¬(∃R. R(v)) instantiated with "is the identity" → ¬(v = λx.x)
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const atom = h.atom(cut, R1)
    const W = h.wire(cut, [{ node: atom, port: { kind: 'head' } }], R1)
    const wArg = h.wire(cut, [{ node: atom, port: { kind: 'arg', index: 0 } }], TERM)
    void wArg
    const d = h.build()
    const out = macroComprehensionInstantiate(d, W, identityComp(), [])

    const e = new DiagramBuilder()
    const ecut = e.cut(e.root)
    const en = e.termNode(ecut, p('\\x. x'))
    e.wire(ecut, [{ node: en, port: { kind: 'output' } }], TERM)
    expect(exploreForm(out)).toBe(exploreForm(e.build()))
  })

  it('duplicates the comprehension across multiple atoms and drops the wire', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const a1 = h.atom(cut, R1)
    const a2 = h.atom(cut, R1)
    const W = h.wire(cut, [
      { node: a1, port: { kind: 'head' } },
      { node: a2, port: { kind: 'head' } },
    ], R1)
    const w = h.wire(cut, [
      { node: a1, port: { kind: 'arg', index: 0 } },
      { node: a2, port: { kind: 'arg', index: 0 } },
    ], TERM)
    const d = h.build()
    const out = macroComprehensionInstantiate(d, W, identityComp(), [])
    expect(termNodes(out)).toHaveLength(2)
    expect(atomNodes(out)).toHaveLength(0)
    expect(out.wires[W]).toBeUndefined()
    // both copies' outputs landed on the one shared arg wire
    expect(out.wires[w]!.endpoints).toHaveLength(2)
  })

  it('with zero atoms it simply removes the ∃R wire, leaving other content untouched', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const W = h.relWire(cut, R1)
    const survivor = h.termNode(cut, p('\\x. x'))
    const d = h.build()
    const out = macroComprehensionInstantiate(d, W, identityComp(), [])
    expect(out.wires[W]).toBeUndefined()
    expect(out.nodes[survivor]?.region).toBe(cut)
  })

  it('rejects a positive wire, a non-relational wire, and boundary/arity mismatches, by name', () => {
    // positive wire: forward instantiation attaches at a positive scope → refuse
    const hp = new DiagramBuilder()
    const Wp = hp.relWire(hp.root, R1) // root positive
    expect(() => macroComprehensionInstantiate(hp.build(), Wp, identityComp(), []))
      .toThrowError(/requires a negative/)
    expect(() => macroComprehensionInstantiate(hp.build(), Wp, identityComp(), [])).toThrow(RuleError)

    // non-relational (TERM) wire: only relational wires carry bodies
    const ht = new DiagramBuilder()
    const cut = ht.cut(ht.root)
    const Wt = ht.wire(cut, [], TERM)
    expect(() => macroComprehensionInstantiate(ht.build(), Wt, identityComp(), []))
      .toThrowError(/not a relation signature/)

    // arity/boundary mismatch: paramComp has 2 boundary wires but arity 1, 0 params given
    const ha = new DiagramBuilder()
    const cutA = ha.cut(ha.root)
    const Wa = ha.relWire(cutA, R1)
    expect(() => macroComprehensionInstantiate(ha.build(), Wa, paramComp(), []))
      .toThrowError(/boundary arithmetic/)
  })

  it('handles a diagonal atom R(x,x): both arg positions collapse onto one term copy', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const atom = h.atom(cut, R2)
    const W = h.wire(cut, [{ node: atom, port: { kind: 'head' } }], R2)
    h.wire(cut, [
      { node: atom, port: { kind: 'arg', index: 0 } },
      { node: atom, port: { kind: 'arg', index: 1 } },
    ], TERM)
    const d = h.build()
    const out = macroComprehensionInstantiate(d, W, arity2IdentComp(), [])
    expect(termNodes(out)).toHaveLength(1)
    expect(out.wires[W]).toBeUndefined()
  })

  it('instantiates at depth 3 (negative) but refuses at depth 2 (positive)', () => {
    const deep = new DiagramBuilder()
    const rDeep = nest(deep, 3)
    const Wdeep = deep.relWire(rDeep, R1)
    expect(() => macroComprehensionInstantiate(deep.build(), Wdeep, identityComp(), [])).not.toThrow()

    const shallow = new DiagramBuilder()
    const rShallow = nest(shallow, 2)
    const Wshallow = shallow.relWire(rShallow, R1)
    expect(() => macroComprehensionInstantiate(shallow.build(), Wshallow, identityComp(), []))
      .toThrowError(/requires a negative/)
  })

  it('splices the copy at the atom’s own (deeper) region, not at the wire scope', () => {
    const h = new DiagramBuilder()
    const c1 = h.cut(h.root) // negative — the wire lives here
    const inner = h.cut(c1) // the atom sits deeper
    const atom = h.atom(inner, R1)
    const W = h.wire(c1, [{ node: atom, port: { kind: 'head' } }], R1)
    h.wire(inner, [{ node: atom, port: { kind: 'arg', index: 0 } }], TERM)
    const d = h.build()
    const out = macroComprehensionInstantiate(d, W, identityComp(), [])
    const terms = termNodes(out)
    expect(terms).toHaveLength(1)
    expect(terms[0]!.region).toBe(inner)
  })
})

describe('macroComprehensionInstantiate — parameters', () => {
  /** cut[ atom on W with arg wire ] plus a parameter line at `paramScope`. */
  function paramHost(paramScope: 'root' | 'cut') {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const atom = h.atom(cut, R1)
    const W = h.wire(cut, [{ node: atom, port: { kind: 'head' } }], R1)
    const wArg = h.wire(cut, [{ node: atom, port: { kind: 'arg', index: 0 } }], TERM)
    const wParam = h.wire(paramScope === 'root' ? h.root : cut, [], TERM)
    return { d: h.build(), cut, W, wArg, wParam }
  }

  it('splices the copy with its parameter port on the GIVEN host wire (root-scoped parameter)', () => {
    const { d, W, wArg, wParam } = paramHost('root')
    const out = macroComprehensionInstantiate(d, W, paramComp(), [wParam])
    expect(out.wires[W]).toBeUndefined()
    const copies = termNodes(out)
    expect(copies).toHaveLength(1)
    // the parameter port rides wParam itself (wire identity preserved), the output rides wArg
    const paramEps = out.wires[wParam]!.endpoints
    expect(paramEps).toHaveLength(1)
    expect(paramEps[0]!.port.kind).toBe('freeVar')
    const argEps = out.wires[wArg]!.endpoints
    expect(argEps).toHaveLength(1)
    expect(argEps[0]!.port.kind).toBe('output')
  })

  it('accepts a parameter scoped at the wire’s own region (at-or-outside admits equality)', () => {
    const { d, cut, W, wParam } = paramHost('cut')
    const out = macroComprehensionInstantiate(d, W, paramComp(), [wParam])
    expect(out.wires[wParam]!.scope).toBe(cut)
    expect(out.wires[wParam]!.endpoints).toHaveLength(1)
  })

  it('refuses a parameter scoped strictly inside the wire’s scope (would be captured)', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const atom = h.atom(cut, R1)
    const W = h.wire(cut, [{ node: atom, port: { kind: 'head' } }], R1)
    h.wire(cut, [{ node: atom, port: { kind: 'arg', index: 0 } }], TERM)
    const inner = h.cut(cut)
    const captured = h.wire(inner, [], TERM)
    const d = h.build()
    expect(() => macroComprehensionInstantiate(d, W, paramComp(), [captured]))
      .toThrowError(/at or outside the target wire's scope/)
  })

  it('attaches the SAME parameter wire to every copy — parameters are shared across instances', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const a1 = h.atom(cut, R1)
    const a2 = h.atom(cut, R1)
    const W = h.wire(cut, [
      { node: a1, port: { kind: 'head' } },
      { node: a2, port: { kind: 'head' } },
    ], R1)
    h.wire(cut, [{ node: a1, port: { kind: 'arg', index: 0 } }], TERM)
    h.wire(cut, [{ node: a2, port: { kind: 'arg', index: 0 } }], TERM)
    const wParam = h.wire(h.root, [], TERM)
    const d = h.build()
    const out = macroComprehensionInstantiate(d, W, paramComp(), [wParam])
    const eps = out.wires[wParam]!.endpoints
    expect(eps).toHaveLength(2)
    expect(new Set(eps.map((ep) => ep.node)).size).toBe(2)
    for (const ep of eps) expect(ep.port.kind).toBe('freeVar')
  })

  it('refuses attachment-count mismatches in both directions', () => {
    const { d, W, wParam } = paramHost('root')
    // too few: paramComp boundary 2, arity 1, 0 params
    expect(() => macroComprehensionInstantiate(d, W, paramComp(), []))
      .toThrowError(/boundary arithmetic/)
    // too many: identityComp boundary 1, arity 1, 1 param
    expect(() => macroComprehensionInstantiate(d, W, identityComp(), [wParam]))
      .toThrowError(/boundary arithmetic/)
  })

  it('refuses a nonexistent parameter wire even when the wire binds zero atoms', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const W = h.relWire(cut, R1)
    const d = h.build()
    expect(() => macroComprehensionInstantiate(d, W, paramComp(), ['ghost']))
      .toThrowError(/does not exist/)
  })

  it('open comprehension: a RELATIONAL parameter rides an outer relation line (replaces the binder spine)', () => {
    // The retired binder-spine mechanism (open comprehension binders) is now a
    // relational parameter: R(x) := S(x) for an outer relation S. The parameter
    // wire is the outer S-line; its scope gate is the same at-or-outside gate.
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const atom = h.atom(cut, R1)
    const W = h.wire(cut, [{ node: atom, port: { kind: 'head' } }], R1)
    h.wire(cut, [{ node: atom, port: { kind: 'arg', index: 0 } }], TERM)
    const sLine = h.relWire(h.root, R1) // outer relation parameter
    const d = h.build()
    const out = macroComprehensionInstantiate(d, W, relParamComp(), [sLine])
    expect(out.wires[W]).toBeUndefined()
    // the inlined inner atom S(x) now rides the outer S-line
    const sEps = out.wires[sLine]!.endpoints
    expect(sEps).toHaveLength(1)
    expect(sEps[0]!.port.kind).toBe('head')
    expect(atomNodes(out)).toHaveLength(1)
  })
})

describe('macroComprehensionInstantiate — flat plusComm parameterized comprehension', () => {
  it('duplicates R(x) := pair(PLUS x b, PLUS b x) across four atoms riding one ambient b-line', () => {
    // Comp body: two term nodes PLUS q q_0 / PLUS q_0 q sharing an output wire;
    // arg stub = q line, param stub = q_0 line.
    const b = new DiagramBuilder()
    const P1 = b.termNode(b.root, p('PLUS q q_0'))
    const P2 = b.termNode(b.root, p('PLUS q_0 q'))
    const wx = b.wire(b.root, [
      { node: P1, port: { kind: 'freeVar', name: 'q' } },
      { node: P2, port: { kind: 'freeVar', name: 'q' } },
    ], TERM)
    const wq = b.wire(b.root, [
      { node: P1, port: { kind: 'freeVar', name: 'q_0' } },
      { node: P2, port: { kind: 'freeVar', name: 'q_0' } },
    ], TERM)
    b.wire(b.root, [
      { node: P1, port: { kind: 'output' } },
      { node: P2, port: { kind: 'output' } },
    ], TERM)
    const comp = mkDiagramWithBoundary(b.build(), [wx, wq])

    // Host: a negative wire W bound by four atoms across the ℕ(a)-induction shape.
    const h = new DiagramBuilder()
    const cut1 = h.cut(h.root)
    const nz = h.termNode(cut1, p('ZERO'))
    const a0 = h.atom(cut1, R1)
    const W = h.wire(cut1, [{ node: a0, port: { kind: 'head' } }], R1)
    const w0 = h.wire(h.root, [
      { node: nz, port: { kind: 'output' } },
      { node: a0, port: { kind: 'arg', index: 0 } },
    ], TERM)
    const cut2 = h.cut(cut1)
    const a1 = h.atom(cut2, R1)
    const ny = h.termNode(cut2, p('SUCC y'))
    h.wire(cut2, [
      { node: a1, port: { kind: 'arg', index: 0 } },
      { node: ny, port: { kind: 'freeVar', name: 'y' } },
    ], TERM)
    const cut3 = h.cut(cut2)
    const a2 = h.atom(cut3, R1)
    h.wire(cut2, [
      { node: ny, port: { kind: 'output' } },
      { node: a2, port: { kind: 'arg', index: 0 } },
    ], TERM)
    const cut4 = h.cut(cut1)
    const a3 = h.atom(cut4, R1)
    const wa = h.wire(h.root, [{ node: a3, port: { kind: 'arg', index: 0 } }], TERM)
    const wb = h.wire(h.root, [], TERM)
    // wire all four atom heads onto the single W (rebuild W with every head)
    void W
    const d0 = h.build()
    // The builder gave a0's head W; give a1..a3 heads onto W too by editing wires.
    const dWires = { ...d0.wires }
    dWires[W] = {
      scope: d0.wires[W]!.scope,
      sig: d0.wires[W]!.sig,
      endpoints: [
        { node: a0, port: { kind: 'head' } },
        { node: a1, port: { kind: 'head' } },
        { node: a2, port: { kind: 'head' } },
        { node: a3, port: { kind: 'head' } },
      ],
    }
    // a1..a3 heads were auto-wired to fresh singleton relational wires; drop those.
    for (const [id, w] of Object.entries(dWires)) {
      if (id === W) continue
      if (w.endpoints.length === 1 && w.endpoints[0]!.port.kind === 'head' &&
        [a1, a2, a3].includes(w.endpoints[0]!.node)) {
        delete dWires[id]
      }
    }
    const d = { ...d0, wires: dWires }

    const out = macroComprehensionInstantiate(d, W, comp, [wb])
    expect(out.wires[W]).toBeUndefined()
    expect(atomNodes(out)).toHaveLength(0)
    // 2 original term nodes (ZERO, SUCC y) + 4 copies × 2 PLUS nodes = 10 term nodes
    expect(termNodes(out)).toHaveLength(10)
    // every copy rides the SAME ambient b-line: 4 copies × 2 freeVar ports
    const bEps = out.wires[wb]!.endpoints
    expect(bEps).toHaveLength(8)
    for (const ep of bEps) expect(ep.port.kind).toBe('freeVar')
    // conclusion copy's stub landed on the a-line (2 freeVar ports)
    expect(out.wires[wa]!.endpoints).toHaveLength(2)
    // base copy's stub joined the ZERO line: 1 output + 2 freeVar
    const zEps = out.wires[w0]!.endpoints
    expect(zEps.filter((ep) => ep.port.kind === 'output')).toHaveLength(1)
    expect(zEps.filter((ep) => ep.port.kind === 'freeVar')).toHaveLength(2)
    // each copy's pair shares one fresh output wire: 4 wires with 2 output endpoints
    const pairWires = Object.values(out.wires).filter(
      (w) => w.endpoints.length === 2 && w.endpoints.every((ep) => ep.port.kind === 'output'),
    )
    expect(pairWires).toHaveLength(4)
  })
})

/* ========================================================================== */
/* ABSTRACTION                                                                */
/* ========================================================================== */

describe('macroComprehensionAbstract — core (replay of applyComprehensionAbstract)', () => {
  it('introduces ∃R and replaces the occurrence by an atom on it', () => {
    // (v = λx.x) ∧ hub(v)  ⟹  ∃R. (R(v) ∧ hub(v))
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('\\x. x'))
    const hub = h.termNode(h.root, p('y'))
    const w = h.wire(h.root, [
      { node: n, port: { kind: 'output' } },
      { node: hub, port: { kind: 'freeVar', name: 'y' } },
    ], TERM)
    const d = h.build()
    const occ = { sel: mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] }), args: [w] }
    const out = macroComprehensionAbstract(d, d.root, identityComp(), [occ])

    const e = new DiagramBuilder()
    const ehub = e.termNode(e.root, p('y'))
    const eatom = e.atom(e.root, R1)
    e.wire(e.root, [{ node: eatom, port: { kind: 'head' } }], R1)
    e.wire(e.root, [
      { node: ehub, port: { kind: 'freeVar', name: 'y' } },
      { node: eatom, port: { kind: 'arg', index: 0 } },
    ], TERM)
    expect(exploreForm(out)).toBe(exploreForm(e.build()))
  })

  it('abstracts several disjoint occurrences into distinct atoms', () => {
    const h = new DiagramBuilder()
    const n1 = h.termNode(h.root, p('\\x. x'))
    const n2 = h.termNode(h.root, p('\\x. x'))
    const w1 = h.wire(h.root, [{ node: n1, port: { kind: 'output' } }], TERM)
    const w2 = h.wire(h.root, [{ node: n2, port: { kind: 'output' } }], TERM)
    const d = h.build()
    const out = macroComprehensionAbstract(d, d.root, identityComp(), [
      { sel: mkSelection(d, { region: d.root, regions: [], nodes: [n1], wires: [] }), args: [w1] },
      { sel: mkSelection(d, { region: d.root, regions: [], nodes: [n2], wires: [] }), args: [w2] },
    ])
    expect(atomNodes(out)).toHaveLength(2)
    expect(termNodes(out)).toHaveLength(0)
  })

  it('rejects an occurrence that does not match the comprehension (fingerprint)', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('\\x. \\y. x'))
    const w = h.wire(h.root, [{ node: n, port: { kind: 'output' } }], TERM)
    const d = h.build()
    const occ = { sel: mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] }), args: [w] }
    expect(() => macroComprehensionAbstract(d, d.root, identityComp(), [occ]))
      .toThrowError(/does not match/)
  })

  it('rejects argument-order mismatches: swapped args change the pinned fingerprint', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('y'))
    const w0 = h.wire(h.root, [{ node: n, port: { kind: 'output' } }], TERM)
    const w1 = h.wire(h.root, [{ node: n, port: { kind: 'freeVar', name: 'y' } }], TERM)
    const d = h.build()
    const mk = (args: readonly WireId[]) => ({
      sel: mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] }),
      args,
    })
    expect(() => macroComprehensionAbstract(d, d.root, binaryComp(), [mk([w1, w0])]))
      .toThrowError(/does not match/)
    expect(() => macroComprehensionAbstract(d, d.root, binaryComp(), [mk([w0, w1])])).not.toThrow()
  })

  it('rejects diagonal args that leave a distinct attachment wire unused', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('y'))
    const w0 = h.wire(h.root, [{ node: n, port: { kind: 'output' } }], TERM)
    h.wire(h.root, [{ node: n, port: { kind: 'freeVar', name: 'y' } }], TERM)
    const d = h.build()
    const occ = { sel: mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] }), args: [w0, w0] }
    expect(() => macroComprehensionAbstract(d, d.root, binaryComp(), [occ]))
      .toThrowError(/is not used by any argument position/)
  })

  it('rejects a negative wrap region and overlapping occurrences', () => {
    // negative wrap: abstraction attaches the witness at a negative scope → refuse
    const hn = new DiagramBuilder()
    const cut = hn.cut(hn.root)
    const n = hn.termNode(cut, p('\\x. x'))
    const wN = hn.wire(cut, [{ node: n, port: { kind: 'output' } }], TERM)
    const dn = hn.build()
    const negOcc = { sel: mkSelection(dn, { region: cut, regions: [], nodes: [n], wires: [] }), args: [wN] }
    expect(() => macroComprehensionAbstract(dn, cut, identityComp(), [negOcc]))
      .toThrowError(/requires a positive/)

    // overlapping: the same occurrence folded twice — the second sees removed nodes
    const ho = new DiagramBuilder()
    const m = ho.termNode(ho.root, p('\\x. x'))
    const wm = ho.wire(ho.root, [{ node: m, port: { kind: 'output' } }], TERM)
    const dO = ho.build()
    const occ = { sel: mkSelection(dO, { region: dO.root, regions: [], nodes: [m], wires: [] }), args: [wm] }
    expect(() => macroComprehensionAbstract(dO, dO.root, identityComp(), [occ, occ])).toThrow()
  })

  it('with zero occurrences it introduces a fresh empty ∃R wire, leaving content intact', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('\\x. x'))
    const d = h.build()
    const out = macroComprehensionAbstract(d, d.root, identityComp(), [])
    // exactly one fresh relational wire, endpoint-free, at the wrap scope
    const rels = relWires(out)
    expect(rels).toHaveLength(1)
    const [, W] = rels[0]!
    expect(W.endpoints).toHaveLength(0)
    expect(W.scope).toBe(d.root)
    // the term node survives untouched
    expect(out.nodes[n]?.region).toBe(d.root)
  })

  it('abstracts inside a doubly-cut (positive) region: ∃R lands at that region', () => {
    const h = new DiagramBuilder()
    const c1 = h.cut(h.root)
    const c2 = h.cut(c1)
    const n = h.termNode(c2, p('\\x. x'))
    const w = h.wire(c2, [{ node: n, port: { kind: 'output' } }], TERM)
    const d = h.build()
    const occ = { sel: mkSelection(d, { region: c2, regions: [], nodes: [n], wires: [] }), args: [w] }
    const out = macroComprehensionAbstract(d, c2, identityComp(), [occ])
    const rels = relWires(out)
    expect(rels).toHaveLength(1)
    expect(rels[0]![1].scope).toBe(c2)
  })

  it('parents the atom at the occurrence anchor region, not the wrap scope', () => {
    const h = new DiagramBuilder()
    const c1 = h.cut(h.root)
    const n = h.termNode(c1, p('\\x. x'))
    const w = h.wire(h.root, [{ node: n, port: { kind: 'output' } }], TERM)
    const d = h.build()
    const occ = { sel: mkSelection(d, { region: c1, regions: [], nodes: [n], wires: [] }), args: [w] }
    const out = macroComprehensionAbstract(d, d.root, identityComp(), [occ])
    const atoms = atomNodes(out)
    expect(atoms).toHaveLength(1)
    expect(atoms[0]!.region).toBe(c1)
  })

  it('attaches the atom arg-i endpoint to args[i], in order', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('y'))
    const w0 = h.wire(h.root, [{ node: n, port: { kind: 'output' } }], TERM)
    const w1 = h.wire(h.root, [{ node: n, port: { kind: 'freeVar', name: 'y' } }], TERM)
    const d = h.build()
    const occ = { sel: mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] }), args: [w0, w1] }
    const out = macroComprehensionAbstract(d, d.root, binaryComp(), [occ])
    expect(out.wires[w0]!.endpoints.map((ep) => ep.port)).toEqual([{ kind: 'arg', index: 0 }])
    expect(out.wires[w1]!.endpoints.map((ep) => ep.port)).toEqual([{ kind: 'arg', index: 1 }])
  })
})

/* ========================================================================== */
/* DIAGONAL ABSTRACTION                                                       */
/* ========================================================================== */

describe('macroComprehensionAbstract — diagonal occurrences', () => {
  it('abstracts φ(x,x): both arg ports land on one wire', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('y'))
    const x = h.wire(h.root, [
      { node: n, port: { kind: 'output' } },
      { node: n, port: { kind: 'freeVar', name: 'y' } },
    ], TERM)
    const d = h.build()
    const occ = { sel: mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] }), args: [x, x] }
    const out = macroComprehensionAbstract(d, d.root, binaryComp(), [occ])
    const atoms = Object.entries(out.nodes).filter(([, m]) => m.kind === 'atom')
    expect(atoms).toHaveLength(1)
    expect(termNodes(out)).toHaveLength(0)
    const atomId = atoms[0]![0]
    const xEps = out.wires[x]!.endpoints
    expect(xEps).toHaveLength(2)
    expect(xEps.every((ep) => ep.node === atomId)).toBe(true)
    expect(xEps.map((ep) => (ep.port.kind === 'arg' ? ep.port.index : -1)).sort()).toEqual([0, 1])
  })

  it('abstracts a triple diagonal ψ(x,x,x): all three arg ports on one wire', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('f g'))
    const x = h.wire(h.root, [
      { node: n, port: { kind: 'output' } },
      { node: n, port: { kind: 'freeVar', name: 'f' } },
      { node: n, port: { kind: 'freeVar', name: 'g' } },
    ], TERM)
    const d = h.build()
    const occ = { sel: mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] }), args: [x, x, x] }
    const out = macroComprehensionAbstract(d, d.root, ternaryComp(), [occ])
    const atoms = Object.entries(out.nodes).filter(([, m]) => m.kind === 'atom')
    expect(atoms).toHaveLength(1)
    const xEps = out.wires[x]!.endpoints
    expect(xEps).toHaveLength(3)
    expect(xEps.map((ep) => (ep.port.kind === 'arg' ? ep.port.index : -1)).sort()).toEqual([0, 1, 2])
  })

  it('abstracts a mixed diagonal ψ(x,x,y): args 0,1 on x and arg 2 on y', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('f g'))
    const x = h.wire(h.root, [
      { node: n, port: { kind: 'output' } },
      { node: n, port: { kind: 'freeVar', name: 'f' } },
    ], TERM)
    const y = h.wire(h.root, [{ node: n, port: { kind: 'freeVar', name: 'g' } }], TERM)
    const d = h.build()
    const occ = { sel: mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] }), args: [x, x, y] }
    const out = macroComprehensionAbstract(d, d.root, ternaryComp(), [occ])
    const atoms = Object.entries(out.nodes).filter(([, m]) => m.kind === 'atom')
    expect(atoms).toHaveLength(1)
    const atomId = atoms[0]![0]
    const xEps = out.wires[x]!.endpoints
    expect(xEps.map((ep) => (ep.port.kind === 'arg' ? ep.port.index : -1)).sort()).toEqual([0, 1])
    const yEps = out.wires[y]!.endpoints
    expect(yEps).toHaveLength(1)
    expect(yEps[0]!.node).toBe(atomId)
    expect(yEps[0]!.port.kind === 'arg' && yEps[0]!.port.index).toBe(2)
  })

  it('a near-diagonal occurrence (one node different) is refused by fingerprint', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('\\z. y'))
    const x = h.wire(h.root, [
      { node: n, port: { kind: 'output' } },
      { node: n, port: { kind: 'freeVar', name: 'y' } },
    ], TERM)
    const d = h.build()
    const occ = { sel: mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] }), args: [x, x] }
    expect(() => macroComprehensionAbstract(d, d.root, binaryComp(), [occ]))
      .toThrowError(/does not match/)
  })

  it('an occurrence matching the UNdiagonalized comp is refused under a diagonal call', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('y'))
    const x = h.wire(h.root, [{ node: n, port: { kind: 'output' } }], TERM)
    h.wire(h.root, [{ node: n, port: { kind: 'freeVar', name: 'y' } }], TERM)
    const d = h.build()
    const occ = { sel: mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] }), args: [x, x] }
    expect(() => macroComprehensionAbstract(d, d.root, binaryComp(), [occ]))
      .toThrowError(/is not used by any argument position/)
  })

  it('a diagonal occurrence is refused under a NON-diagonal call (arg wire not an attachment)', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('y'))
    const x = h.wire(h.root, [
      { node: n, port: { kind: 'output' } },
      { node: n, port: { kind: 'freeVar', name: 'y' } },
    ], TERM)
    const z = h.wire(h.root, [], TERM)
    const d = h.build()
    const occ = { sel: mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] }), args: [x, z] }
    expect(() => macroComprehensionAbstract(d, d.root, binaryComp(), [occ]))
      .toThrowError(/is not one of the occurrence's attachment wires/)
  })

  it('the polarity gate still fires for a diagonal occurrence in a negative region', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const n = h.termNode(cut, p('y'))
    const x = h.wire(cut, [
      { node: n, port: { kind: 'output' } },
      { node: n, port: { kind: 'freeVar', name: 'y' } },
    ], TERM)
    const d = h.build()
    const occ = { sel: mkSelection(d, { region: cut, regions: [], nodes: [n], wires: [] }), args: [x, x] }
    expect(() => macroComprehensionAbstract(d, cut, binaryComp(), [occ]))
      .toThrowError(/requires a positive/)
  })

  it('refuses an arity mismatch: too few argument positions for the comp', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('y'))
    const x = h.wire(h.root, [
      { node: n, port: { kind: 'output' } },
      { node: n, port: { kind: 'freeVar', name: 'y' } },
    ], TERM)
    const d = h.build()
    const occ = { sel: mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] }), args: [x] }
    expect(() => macroComprehensionAbstract(d, d.root, binaryComp(), [occ]))
      .toThrowError(/arity 2 but 1 argument/)
  })

  it('rejects aliasing confusion: an honest (1,2)-merge verifies, a (0,1)-merge call refuses', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('f g'))
    const pp = h.wire(h.root, [{ node: n, port: { kind: 'output' } }], TERM)
    const q = h.wire(h.root, [
      { node: n, port: { kind: 'freeVar', name: 'f' } },
      { node: n, port: { kind: 'freeVar', name: 'g' } },
    ], TERM)
    const d = h.build()
    const mk = (args: readonly WireId[]) => ({
      sel: mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] }),
      args,
    })
    expect(() => macroComprehensionAbstract(d, d.root, ternaryComp(), [mk([pp, q, q])])).not.toThrow()
    expect(() => macroComprehensionAbstract(d, d.root, ternaryComp(), [mk([q, q, pp])]))
      .toThrowError(/does not match/)
  })
})

/* ========================================================================== */
/* PLAN-16 ADVERSARIAL — diagonalized-form confusion                          */
/* ========================================================================== */

describe('Plan 16 adversarial — diagonalized-form confusion', () => {
  /** (0,1)-merge occurrence of `f g`: out+f on x, g on y. */
  function merge01() {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('f g'))
    const x = h.wire(h.root, [
      { node: n, port: { kind: 'output' } },
      { node: n, port: { kind: 'freeVar', name: 'f' } },
    ], TERM)
    const y = h.wire(h.root, [{ node: n, port: { kind: 'freeVar', name: 'g' } }], TERM)
    const d = h.build()
    const sel = () => mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] })
    return { d, x, y, sel }
  }

  it('the honest (0,1)-merge call VERIFIES', () => {
    const { d, x, y, sel } = merge01()
    expect(() => macroComprehensionAbstract(d, d.root, ternaryComp(), [{ sel: sel(), args: [x, x, y] }]))
      .not.toThrow()
  })

  it('a (0,1)-merge occurrence is REFUSED under a (0,2)-merge call', () => {
    const { d, x, y, sel } = merge01()
    expect(() => macroComprehensionAbstract(d, d.root, ternaryComp(), [{ sel: sel(), args: [x, y, x] }]))
      .toThrowError(/does not match/)
  })

  it('a (0,1)-merge occurrence is REFUSED under a (1,2)-merge call', () => {
    const { d, x, y, sel } = merge01()
    expect(() => macroComprehensionAbstract(d, d.root, ternaryComp(), [{ sel: sel(), args: [x, y, y] }]))
      .toThrowError(/does not match/)
  })

  it('a (0,1)-merge occurrence is REFUSED under a FULLY diagonal (0,1,2) call (unused y)', () => {
    const { d, x, sel } = merge01()
    expect(() => macroComprehensionAbstract(d, d.root, ternaryComp(), [{ sel: sel(), args: [x, x, x] }]))
      .toThrowError(/is not used by any argument position/)
  })

  it('a fully-diagonal occurrence φ(x,x,x) is REFUSED under a partial (0,1) call naming a non-attachment', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('f g'))
    const x = h.wire(h.root, [
      { node: n, port: { kind: 'output' } },
      { node: n, port: { kind: 'freeVar', name: 'f' } },
      { node: n, port: { kind: 'freeVar', name: 'g' } },
    ], TERM)
    const z = h.wire(h.root, [], TERM)
    const d = h.build()
    const sel = () => mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] })
    expect(() => macroComprehensionAbstract(d, d.root, ternaryComp(), [{ sel: sel(), args: [x, x, z] }]))
      .toThrowError(/is not one of the occurrence's attachment wires/)
  })

  it('a dangling third wire hidden behind an aliased pair is REFUSED, naming the wire', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('f g'))
    const x = h.wire(h.root, [
      { node: n, port: { kind: 'output' } },
      { node: n, port: { kind: 'freeVar', name: 'f' } },
    ], TERM)
    const w = h.wire(h.root, [{ node: n, port: { kind: 'freeVar', name: 'g' } }], TERM)
    const d = h.build()
    const sel = () => mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] })
    expect(() => macroComprehensionAbstract(d, d.root, binaryComp(), [{ sel: sel(), args: [x, x] }]))
      .toThrowError(new RegExp(`attachment wire '${w}' is not used by any argument position`))
  })

  it('a diagonal ∃R.R(x,x) at a POSITIVE region refuses instantiation', () => {
    const h = new DiagramBuilder()
    const atom = h.atom(h.root, R2)
    const W = h.wire(h.root, [{ node: atom, port: { kind: 'head' } }], R2)
    h.wire(h.root, [
      { node: atom, port: { kind: 'arg', index: 0 } },
      { node: atom, port: { kind: 'arg', index: 1 } },
    ], TERM)
    const d = h.build()
    expect(() => macroComprehensionInstantiate(d, W, binaryComp(), []))
      .toThrowError(/requires a negative/)
  })
})

/* ========================================================================== */
/* ROUND-TRIP — orientation-pairing proof (instantiate ⟷ abstract involution)  */
/* ========================================================================== */

describe('macro round-trip: abstraction and instantiation are mutually inverse', () => {
  it('abstract-forward then instantiate-backward at a positive scope is the identity on φ(x,x)', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('y'))
    const x = h.wire(h.root, [
      { node: n, port: { kind: 'output' } },
      { node: n, port: { kind: 'freeVar', name: 'y' } },
    ], TERM)
    const d0 = h.build()
    const occ = { sel: mkSelection(d0, { region: d0.root, regions: [], nodes: [n], wires: [] }), args: [x, x] }
    const abs = macroComprehensionAbstract(d0, d0.root, binaryComp(), [occ], 'forward')
    // ∃R.R(x,x) at the positive root: instantiate backward returns φ(x,x)
    const rels = relWires(abs)
    expect(rels).toHaveLength(1)
    const inst = macroComprehensionInstantiate(abs, rels[0]![0], binaryComp(), [], 'backward')
    expect(exploreForm(inst)).toBe(exploreForm(d0))
  })

  it('instantiate-forward then abstract-backward at a negative scope is the identity on ∃R.R(x,x)', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const atom = h.atom(cut, R2)
    const W = h.wire(cut, [{ node: atom, port: { kind: 'head' } }], R2)
    const x = h.wire(cut, [
      { node: atom, port: { kind: 'arg', index: 0 } },
      { node: atom, port: { kind: 'arg', index: 1 } },
    ], TERM)
    const d0 = h.build()
    const inst = macroComprehensionInstantiate(d0, W, binaryComp(), [], 'forward')
    // φ(x,x) at the negative cut: abstract backward returns ∃R.R(x,x)
    const phiNode = termNodes(inst)[0]!
    const phiId = Object.entries(inst.nodes).find(([, m]) => m === phiNode)![0]
    const occ = { sel: mkSelection(inst, { region: cut, regions: [], nodes: [phiId], wires: [] }), args: [x, x] }
    const abs = macroComprehensionAbstract(inst, cut, binaryComp(), [occ], 'backward')
    expect(exploreForm(abs)).toBe(exploreForm(d0))
  })

  it('the instantiated φ(x,x) re-abstracts DIAGONALLY and REFUSES a non-diagonal re-abstraction', () => {
    // ∃R.R(x,x) with the wire at a negative cut whose atom lives one cut deeper
    // (a positive region); instantiation drops φ(x,x) there, where abstraction is legal.
    const h = new DiagramBuilder()
    const cut1 = h.cut(h.root)
    const inner = h.cut(cut1)
    const atom = h.atom(inner, R2)
    const W = h.wire(cut1, [{ node: atom, port: { kind: 'head' } }], R2)
    const x = h.wire(inner, [
      { node: atom, port: { kind: 'arg', index: 0 } },
      { node: atom, port: { kind: 'arg', index: 1 } },
    ], TERM)
    const zId = h.wire(inner, [], TERM) // real, independent decoy wire
    const inst = macroComprehensionInstantiate(h.build(), W, binaryComp(), [], 'forward')
    const phiId = Object.entries(inst.nodes).find(([, m]) => m.kind === 'term')![0]
    const region = inst.nodes[phiId]!.region
    const sel = () => mkSelection(inst, { region, regions: [], nodes: [phiId], wires: [] })

    const out = macroComprehensionAbstract(inst, region, binaryComp(), [{ sel: sel(), args: [x, x] }])
    const atoms = Object.entries(out.nodes).filter(([, m]) => m.kind === 'atom')
    expect(atoms).toHaveLength(1)
    const xEps = out.wires[x]!.endpoints
    expect(xEps).toHaveLength(2)
    expect(xEps.every((ep) => ep.node === atoms[0]![0])).toBe(true)

    expect(() => macroComprehensionAbstract(inst, region, binaryComp(), [{ sel: sel(), args: [x, zId] }]))
      .toThrowError(/is not one of the occurrence's attachment wires/)
  })
})

/* ========================================================================== */
/* GATE PARITY SWEEP (equational-gates.test.ts, block 2)                       */
/* ========================================================================== */

describe('comprehension gate parity across depths 0..3', () => {
  for (let depth = 0; depth <= 3; depth++) {
    const positive = depth % 2 === 0
    it(`depth ${depth} (${positive ? 'positive' : 'negative'}): abstract ${positive ? 'allowed' : 'rejected'}, instantiate ${positive ? 'rejected' : 'allowed'}`, () => {
      // Abstract host: a term node λx.x to abstract.
      const ha = new DiagramBuilder()
      const region = nest(ha, depth)
      const n = ha.termNode(region, p('\\x. x'))
      const w = ha.wire(region, [{ node: n, port: { kind: 'output' } }], TERM)
      const da = ha.build()
      const occ = { sel: mkSelection(da, { region, regions: [], nodes: [n], wires: [] }), args: [w] }

      // Instantiate host: a bare ∃R wire at the same depth.
      const hi = new DiagramBuilder()
      const regionI = nest(hi, depth)
      const W = hi.relWire(regionI, R1)
      const di = hi.build()

      if (positive) {
        expect(() => macroComprehensionAbstract(da, region, identityComp(), [occ])).not.toThrow()
        expect(() => macroComprehensionInstantiate(di, W, identityComp(), []))
          .toThrowError(/requires a negative/)
      } else {
        expect(() => macroComprehensionAbstract(da, region, identityComp(), [occ]))
          .toThrowError(/requires a positive/)
        expect(() => macroComprehensionInstantiate(di, W, identityComp(), [])).not.toThrow()
      }
    })
  }
})

/* ========================================================================== */
/* NEW POWER — partial expansion the monolithic rule could not express         */
/* ========================================================================== */

describe('new power: instantiation can leave an occurrence folded', () => {
  it('unfolds all-but-one atom, differs from full expansion, then completes to equal the macro', () => {
    // Two atoms on one negative ∃R wire, each on its own arg line.
    const build = () => {
      const h = new DiagramBuilder()
      const cut = h.cut(h.root)
      const a1 = h.atom(cut, R1)
      const a2 = h.atom(cut, R1)
      const W = h.wire(cut, [
        { node: a1, port: { kind: 'head' } },
        { node: a2, port: { kind: 'head' } },
      ], R1)
      const w1 = h.wire(cut, [{ node: a1, port: { kind: 'arg', index: 0 } }], TERM)
      const w2 = h.wire(cut, [{ node: a2, port: { kind: 'arg', index: 0 } }], TERM)
      return { d: h.build(), cut, a1, a2, W, w1, w2 }
    }

    const full = build()
    const fullOut = macroComprehensionInstantiate(full.d, full.W, identityComp(), [])

    // Partial: attach the body, unfold only a1, leaving a2 folded.
    const part = build()
    const attached = applyBodyAttach(part.d, part.W, identityComp(), [], 'forward')
    const partial = applyUnfold(attached, part.a1, () => undefined)

    // The wire persists, still carries its body, and a2 remains a folded atom.
    expect(partial.wires[part.W]).toBeDefined()
    const bodyStill = partial.wires[part.W]!.endpoints.some(
      (ep) => ep.port.kind === 'output' && partial.nodes[ep.node]?.kind === 'body',
    )
    expect(bodyStill).toBe(true)
    expect(partial.nodes[part.a2]?.kind).toBe('atom')
    expect(partial.nodes[part.a1]).toBeUndefined()

    // Partial expansion is NOT the fully-instantiated form.
    expect(exploreForm(partial)).not.toBe(exploreForm(fullOut))

    // Complete it by hand: unfold the last atom, detach the body, drop the wire.
    const bodyId = partial.wires[part.W]!.endpoints.find(
      (ep) => ep.port.kind === 'output' && partial.nodes[ep.node]?.kind === 'body',
    )!.node
    const done = applyVacuousElim(
      applyBodyDetach(applyUnfold(partial, part.a2, () => undefined), bodyId, 'backward'),
      part.W,
    )
    expect(exploreForm(done)).toBe(exploreForm(fullOut))
  })
})
