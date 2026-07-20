import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagram } from '../../../src/kernel/diagram/diagram'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { exploreForm } from '../../../src/kernel/diagram/canonical/explore'
import { findOccurrences } from '../../../src/kernel/diagram/subgraph/match'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { applyRelUnfold, applyRelFold } from '../../../src/kernel/rules/reldef'
import type { DiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import type { Endpoint } from '../../../src/kernel/diagram/diagram'

const p = (s: string) => parseTerm(s)

// ===========================================================================
// PART A2 — LABELING COLLISION ATTACKS.
// The soundness of relFold / comprehension / theorem citation rests entirely on
// exploreForm being a COMPLETE invariant: two NON-isomorphic diagrams must get
// DIFFERENT forms. A form collision here is a kernel-gate conflation (CRITICAL):
// relFold would fold a near-miss occurrence to the reference. Every pair below
// is non-isomorphic by construction; each asserts the forms differ.
// ===========================================================================

describe('exploreForm collision resistance (non-iso pairs must differ)', () => {
  it('same node/wire multiset, different connectivity: 3-cycle vs 2-cycle+self-loop', () => {
    // Three `y` nodes (ports out, v0=y). A wire joins one out to one v0.
    const cyc3 = () => {
      const b = new DiagramBuilder()
      const A = b.termNode(b.root, p('y'))
      const B = b.termNode(b.root, p('y'))
      const C = b.termNode(b.root, p('y'))
      b.wire(b.root, [{ node: A, port: { kind: 'output' } }, { node: B, port: { kind: 'freeVar', name: 'y' } }])
      b.wire(b.root, [{ node: B, port: { kind: 'output' } }, { node: C, port: { kind: 'freeVar', name: 'y' } }])
      b.wire(b.root, [{ node: C, port: { kind: 'output' } }, { node: A, port: { kind: 'freeVar', name: 'y' } }])
      return b.build()
    }
    const cyc2loop = () => {
      const b = new DiagramBuilder()
      const A = b.termNode(b.root, p('y'))
      const B = b.termNode(b.root, p('y'))
      const C = b.termNode(b.root, p('y'))
      b.wire(b.root, [{ node: A, port: { kind: 'output' } }, { node: B, port: { kind: 'freeVar', name: 'y' } }])
      b.wire(b.root, [{ node: B, port: { kind: 'output' } }, { node: A, port: { kind: 'freeVar', name: 'y' } }])
      b.wire(b.root, [{ node: C, port: { kind: 'output' } }, { node: C, port: { kind: 'freeVar', name: 'y' } }])
      return b.build()
    }
    // identical multiset: 3 `y` nodes, 3 two-endpoint wires, yet non-isomorphic
    expect(exploreForm(cyc3())).not.toBe(exploreForm(cyc2loop()))
  })

  it('same region count, different nesting: chain root>c1>c2>c3 vs root>{c1>c2, c3}', () => {
    const chain = () => {
      const b = new DiagramBuilder()
      const c1 = b.cut(b.root)
      const c2 = b.cut(c1)
      b.cut(c2)
      return b.build()
    }
    const branch = () => {
      const b = new DiagramBuilder()
      const c1 = b.cut(b.root)
      b.cut(c1)
      b.cut(b.root)
      return b.build()
    }
    expect(exploreForm(chain())).not.toBe(exploreForm(branch()))
  })

  it('positional port role: a hub wired to arg-position 0 vs 1 of `p q`', () => {
    // N = `p q` (ports out, v0=p, v1=q). M = `\x.x` (out). The wire hits v0 or v1.
    const wireTo = (freeVar: string) => {
      const b = new DiagramBuilder()
      const N = b.termNode(b.root, p('p q'))
      const M = b.termNode(b.root, p('\\x. x'))
      b.wire(b.root, [{ node: M, port: { kind: 'output' } }, { node: N, port: { kind: 'freeVar', name: freeVar } }])
      return b.build()
    }
    // p is the function head, q the argument — de Bruijn-distinct roles
    expect(exploreForm(wireTo('p'))).not.toBe(exploreForm(wireTo('q')))
  })

  it('alpha-distinct term bodies are distinguished (not collapsed)', () => {
    const single = (t: string) => {
      const b = new DiagramBuilder()
      b.termNode(b.root, p(t))
      return b.build()
    }
    expect(exploreForm(single('\\x. \\y. x y'))).not.toBe(exploreForm(single('\\x. \\y. y x')))
  })

  it('exact form is NOT modulo beta-eta: a redex differs from its normal form', () => {
    const single = (t: string) => {
      const b = new DiagramBuilder()
      b.termNode(b.root, p(t))
      return b.build()
    }
    expect(exploreForm(single('(\\x. x) y'))).not.toBe(exploreForm(single('y')))
  })

  it('a wire is a SET: endpoint storage order does not affect the form', () => {
    // Two distinguishable nodes on one shared wire, stored [A,B] vs [B,A].
    // These are the same diagram; the forms must be equal. The random relabel
    // property test never reorders endpoints, so this is the only guard on the
    // endpoint-multiset canonicalization (removing serializeWith's endpoint sort
    // makes these forms differ).
    const mk = (order: 'AB' | 'BA') => {
      const A = { node: 'nA', port: { kind: 'output' } } as const
      const B = { node: 'nB', port: { kind: 'output' } } as const
      return mkDiagram({
        root: 'r0',
        regions: { r0: { kind: 'sheet' } },
        nodes: {
          nA: { kind: 'term', region: 'r0', term: p('\\x. x') },
          nB: { kind: 'term', region: 'r0', term: p('\\x. \\y. x') },
        },
        wires: { w0: { scope: 'r0', endpoints: order === 'AB' ? [A, B] : [B, A] } },
      })
    }
    expect(exploreForm(mk('AB'))).toBe(exploreForm(mk('BA')))
  })

  it('symmetric wire members: which node pairs share a wire changes the form', () => {
    // Four distinguishable nodes A=`\x.x`, B=`\x.\y.x`, C=`\x.\y.y`, D=`z`.
    // Group them into two shared output wires two different ways.
    const build = (which: 'AB_CD' | 'AC_BD') => {
      const b = new DiagramBuilder()
      const A = b.termNode(b.root, p('\\x. x'))
      const B = b.termNode(b.root, p('\\x. \\y. x'))
      const C = b.termNode(b.root, p('\\x. \\y. y'))
      const D = b.termNode(b.root, p('z'))
      const o = (n: string): Endpoint => ({ node: n, port: { kind: 'output' } })
      if (which === 'AB_CD') {
        b.wire(b.root, [o(A), o(B)])
        b.wire(b.root, [o(C), o(D)])
      } else {
        b.wire(b.root, [o(A), o(C)])
        b.wire(b.root, [o(B), o(D)])
      }
      return b.build()
    }
    // pairing {A,B},{C,D} vs {A,C},{B,D} are non-isomorphic (nodes are all distinct)
    expect(exploreForm(build('AB_CD'))).not.toBe(exploreForm(build('AC_BD')))
  })
})

// ===========================================================================
// PART A3 — BARE-BOUNDARY ABUSE (scope gates on the seeded path).
// ===========================================================================

describe('bare boundary seeded matching — scope gates', () => {
  // Pattern: a single bare boundary wire scoped at the root (no endpoints).
  function bareBoundaryPattern() {
    const b = new DiagramBuilder()
    const bw = b.wire(b.root, []) // bare, root-scoped
    return mkDiagramWithBoundary(b.build(), [bw])
  }

  it('unseeded bare boundary is refused (determinism over guessing)', () => {
    const b = new DiagramBuilder()
    b.termNode(b.root, p('\\x. x'))
    expect(() => findOccurrences(b.build(), bareBoundaryPattern(), { fuel: 50 })).toThrow(/supply its attachment/)
  })

  it('seeded bare boundary succeeds and its image is the supplied wire', () => {
    const b = new DiagramBuilder()
    const n = b.termNode(b.root, p('\\x. x'))
    const w = b.wire(b.root, [{ node: n, port: { kind: 'output' } }])
    const host = b.build()
    const r = findOccurrences(host, bareBoundaryPattern(), { fuel: 50, inRegion: 'r0', attachments: [w] })
    expect(r.matches.length).toBeGreaterThanOrEqual(1)
    for (const m of r.matches) expect(m.attachments).toEqual([w])
  })

  it('seeded bare boundary is REFUSED when the supplied wire is not visible from R (scope gate)', () => {
    // Host: a cut containing a node; the wire we seed is scoped INSIDE the cut,
    // but we match at the root — the seam wire must be visible at R.
    const b = new DiagramBuilder()
    const c = b.cut(b.root)
    const n = b.termNode(c, p('\\x. x'))
    const wInside = b.wire(c, [{ node: n, port: { kind: 'output' } }]) // scoped in the cut
    const host = b.build()
    // match at the root: wInside.scope = c is NOT an ancestor-or-equal of r0
    const r = findOccurrences(host, bareBoundaryPattern(), { fuel: 50, inRegion: 'r0', attachments: [wInside] })
    expect(r.matches).toHaveLength(0)
  })

  it('a bare boundary wire must be scoped at the pattern root (seam rule)', () => {
    // Bare boundary wire scoped inside a pattern cut → refused up front.
    const b = new DiagramBuilder()
    const c = b.cut(b.root)
    const bw = b.wire(c, []) // bare, but scoped below the root
    expect(() => mkDiagramWithBoundary(b.build(), [bw]))
      .toThrow(/must be scoped at the diagram root/)
  })
})

// ===========================================================================
// PART A4 — MODE CONFUSION: exact must not consult beta-eta; betaEta preserves
// the undecided report contract through the rewrite.
// ===========================================================================

describe('mode confusion', () => {
  it('exact mode never reports undecided even on a non-normalizing node', () => {
    const omega = '(\\x. x x) (\\x. x x)'
    const pb = new DiagramBuilder()
    pb.termNode(pb.root, p(omega))
    const pattern = mkDiagramWithBoundary(pb.build(), [])
    const hb = new DiagramBuilder()
    hb.termNode(hb.root, p(omega))
    const r = findOccurrences(hb.build(), pattern, { fuel: 3, mode: 'exact', inRegion: 'r0' })
    expect(r.undecided).toHaveLength(0)
    expect(r.matches).toHaveLength(1)
  })

  it('betaEta mode surfaces an undecided pair when a candidate exhausts fuel', () => {
    // Closed single-node pattern whose beta-eta comparison exhausts the fuel and
    // must be REPORTED as undecided, not swallowed.
    const pb2 = new DiagramBuilder()
    pb2.termNode(pb2.root, p('(\\x. x) ((\\x. x) ((\\x. x) z))'))
    const pattern = mkDiagramWithBoundary(pb2.build(), [])
    const hb = new DiagramBuilder()
    hb.termNode(hb.root, p('z'))
    const r = findOccurrences(hb.build(), pattern, { fuel: 1, mode: 'betaEta', inRegion: 'r0' })
    // fuel=1 cannot normalize the 3-redex chain → undecided pair reported
    expect(r.undecided.length).toBeGreaterThanOrEqual(1)
    expect(r.matches).toHaveLength(0)
  })
})

// ===========================================================================
// PART A1 — relFold near-miss refusals (SOUNDNESS-CRITICAL GATE, end-to-end).
// The occurrence is built to be ALMOST the relation body; applyRelFold's
// boundary-pinned exact form gate must refuse each. A near-miss that folds is a
// kernel soundness bug.
// ===========================================================================

describe('relFold near-miss refusals (exact boundary-pinned gate)', () => {
  // Body of R: node `y` (its v_y is the arg line / boundary) whose output feeds
  // the free var `w` of a tail node. `tail` picks the tail term.
  function bodyR(tail: string): DiagramWithBoundary {
    const b = new DiagramBuilder()
    const tA = b.termNode(b.root, p('y'))
    const tB = b.termNode(b.root, p(tail))
    b.wire(b.root, [
      { node: tA, port: { kind: 'output' } },
      { node: tB, port: { kind: 'freeVar', name: 'w' } },
    ])
    const bound = b.wire(b.root, [{ node: tA, port: { kind: 'freeVar', name: 'y' } }])
    return mkDiagramWithBoundary(b.build(), [bound])
  }
  // A ref of `defId` (arity 1) with arg-0 wired to a carrier — the fold target.
  function refHost(defId: string) {
    const b = new DiagramBuilder()
    const node = b.ref(b.root, defId, 1)
    const carrier = b.termNode(b.root, p('a'))
    const wArg = b.wire(b.root, [
      { node, port: { kind: 'arg', index: 0 } },
      { node: carrier, port: { kind: 'freeVar', name: 'a' } },
    ])
    return { d: b.build(), node, carrier, wArg }
  }
  // Everything the unfold inlined (all nodes except the carrier) + its internal wires.
  function bodySelection(d: ReturnType<DiagramBuilder['build']>, carrier: string) {
    const bodyNodes = Object.keys(d.nodes).filter((id) => id !== carrier)
    const set = new Set(bodyNodes)
    const internal = Object.keys(d.wires).filter((wid) => {
      const eps = d.wires[wid]!.endpoints
      return eps.length > 0 && eps.every((ep) => set.has(ep.node)) && d.wires[wid]!.scope === d.root
    })
    return mkSelection(d, { region: d.root, regions: [], nodes: bodyNodes, wires: internal })
  }

  it('CONTROL: the exact body folds successfully (unfold → fold round-trip)', () => {
    const relations = new Map([['R', bodyR('w')]])
    const { d, node, carrier, wArg } = refHost('R')
    const un = applyRelUnfold(d, node, relations)
    const sel = bodySelection(un, carrier)
    expect(() => applyRelFold(un, sel, 'R', [wArg], relations)).not.toThrow()
  })

  it('REFUSES a beta-eta-equal but structurally different tail (form is exact, not modulo beta-eta)', () => {
    // Unfold RB (tail `(\u. u) w`, which beta-reduces to `w`), then try to fold
    // as R (tail `w`). The exact gate must refuse: relFold does not fold up to
    // beta-eta even when the two bodies are convertible.
    const relations = new Map([['R', bodyR('w')], ['RB', bodyR('(\\u. u) w')]])
    const { d, node, carrier, wArg } = refHost('RB')
    const un = applyRelUnfold(d, node, relations)
    const sel = bodySelection(un, carrier)
    expect(() => applyRelFold(un, sel, 'R', [wArg], relations)).toThrow(/does not match relation 'R'/)
  })

  // The remaining structural near-misses hit the exact gate function directly
  // (exploreForm boundary-pinned) — the same predicate applyRelFold evaluates —
  // so the modeling of extraction never masks a form collision.
  it('GATE: one extra node makes the boundary-pinned form differ', () => {
    const body = bodyR('w')
    const bodyForm = exploreForm(body.diagram, body.boundary)
    // near-miss: the body plus one extra `\x.x` node
    const b = new DiagramBuilder()
    const tA = b.termNode(b.root, p('y'))
    const tB = b.termNode(b.root, p('w'))
    b.wire(b.root, [{ node: tA, port: { kind: 'output' } }, { node: tB, port: { kind: 'freeVar', name: 'w' } }])
    const bound = b.wire(b.root, [{ node: tA, port: { kind: 'freeVar', name: 'y' } }])
    b.termNode(b.root, p('\\x. x'))
    expect(exploreForm(b.build(), [bound])).not.toBe(bodyForm)
  })

  it('GATE: a missing internal endpoint makes the boundary-pinned form differ', () => {
    const body = bodyR('w')
    const bodyForm = exploreForm(body.diagram, body.boundary)
    // near-miss: identical nodes, but tA.out and tB.v_w are NOT joined
    const b = new DiagramBuilder()
    const tA = b.termNode(b.root, p('y'))
    b.termNode(b.root, p('w')) // tB, its v_w left as an auto singleton
    const bound = b.wire(b.root, [{ node: tA, port: { kind: 'freeVar', name: 'y' } }])
    expect(exploreForm(b.build(), [bound])).not.toBe(bodyForm)
  })

  it('boundary ORDER is part of the gate: an asymmetric arity-2 body distinguishes its two boundary lines', () => {
    // Body: node `f g` (v0=f function head, v1=g argument) — two boundary lines
    // on distinguishable positional roles. Swapping the pin order changes the
    // form, so folding with permuted args cannot conflate the two argument slots.
    const b = new DiagramBuilder()
    const n = b.termNode(b.root, p('f g'))
    const b0 = b.wire(b.root, [{ node: n, port: { kind: 'freeVar', name: 'f' } }])
    const b1 = b.wire(b.root, [{ node: n, port: { kind: 'freeVar', name: 'g' } }])
    const d = b.build()
    expect(exploreForm(d, [b0, b1])).not.toBe(exploreForm(d, [b1, b0]))
  })
})
