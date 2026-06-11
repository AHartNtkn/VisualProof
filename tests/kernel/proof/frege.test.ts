import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import type { Definitions } from '../../../src/kernel/rules/definitions'
import { replayProof, type ProofContext, type ProofStep } from '../../../src/kernel/proof/step'
import { checkTheorem, type Theorem } from '../../../src/kernel/proof/theorem'
import { polarity } from '../../../src/kernel/diagram/regions'

const consts = new Set(['ZERO', 'SUCC', 'PLUS'])
const p = (s: string) => parseTerm(s, consts)
const noConsts = new Set<string>()
const pp = (s: string) => parseTerm(s, noConsts)

const defs: Definitions = {
  ZERO: pp('\\f. \\x. x'),
  SUCC: pp('\\n. \\f. \\x. f (n f x)'),
  PLUS: pp('\\m. \\n. \\f. \\x. m f (n f x)'),
}
const ctx: ProofContext = { definitions: defs, theorems: new Map() }

describe('Frege arithmetic: blank-side ℕ theorems', () => {
  it('z = ZERO ⟹ ℕ(z) replays and checks as a theorem', () => {
    // lhs: a single ZERO node whose output is the boundary wire
    const l = new DiagramBuilder()
    const nz = l.termNode(l.root, p('ZERO'))
    const wz = l.wire(l.root, [{ node: nz, port: { kind: 'output' } }])
    const lhsDiagram = l.build()
    const lhs = mkDiagramWithBoundary(lhsDiagram, [wz])

    // Derivation strategy (each step's ids are computed from the PREVIOUS
    // replay result — write the test as an incremental script):
    // 1. doubleCutIntro on the empty selection at root           → cO[ cI[] ]
    // 2. vacuousIntro(arity 1) at cO wrapping {regions: [cI]}    → cO[ rB[ cI[] ] ]
    // 3. open insertion into rB (negative): the BASE+CLOSURE pattern —
    //    stub(1)[ nZ'(ZERO) →w0→ A0.arg0 ;
    //             cut2[ A1.arg0 —wy— nS(SUCC y).y ; nS.out —ws— A2.arg0 ; cut3[ A2 ] ] ]
    //    with binders {stub: rB}                                  → cO[ rB[ base, Cl, cI[] ] ]
    // 4. open iteration of {A0} (just the atom, attachments = [w0 image])
    //    into cI                                                  → cI[ A3.arg0 on w0Host ]
    // 5. wireJoin(boundary wz, w0Host): inner scope is rB —
    //    polarity(rB) is NEGATIVE (inside cO) → join allowed; the merged wire
    //    keeps the OUTER id wz (root-scoped boundary survives ✓)
    // After step 5 the diagram reads: z=ZERO ∧ ¬∃R…— wait — the joined wire
    // identifies the base's zero-argument with the boundary z. The captured
    // RHS therefore defines ℕ with the base R(x₀) sharing x₀ = z's line —
    // a faithful ℕ(z) for z carrying ZERO: base R(z), closure, ¬R(z) gives
    // ¬∃R¬(R(z) ∧ Cl → R(z)) … the shape is degenerate-but-true unless the
    // base keeps its OWN zero. PREFERRED derivation instead of step 5:
    // 5'. iterate the lhs ZERO node nz (closed iteration, attachments [wz])
    //     into rB, then wireJoin its output-copy wire with w0Host inside rB.
    // The test below follows 1–4 + 5' and CAPTURES the result as rhs.
    let cur = lhsDiagram
    const steps: ProofStep[] = []
    const push = (s: ProofStep): void => {
      steps.push(s)
      cur = replayProof(cur, [s], ctx)
    }

    push({ rule: 'doubleCutIntro', sel: mkSelection(cur, { region: cur.root, regions: [], nodes: [], wires: [] }) })
    const cO = Object.entries(cur.regions).find(([id, r]) => r.kind === 'cut' && r.parent === cur.root && lhsDiagram.regions[id] === undefined)![0]
    const cI = Object.entries(cur.regions).find(([, r]) => r.kind === 'cut' && r.parent === cO)![0]

    push({ rule: 'vacuousIntro', sel: mkSelection(cur, { region: cO, regions: [cI], nodes: [], wires: [] }), arity: 1 })
    const rB = Object.entries(cur.regions).find(([, r]) => r.kind === 'bubble')![0]
    expect(polarity(cur, rB)).toBe('negative')

    // base+closure open pattern
    const b = new DiagramBuilder()
    const stub = b.bubble(b.root, 1)
    const bz = b.termNode(stub, p('ZERO'))
    const a0 = b.atom(stub, stub)
    b.wire(stub, [
      { node: bz, port: { kind: 'output' } },
      { node: a0, port: { kind: 'arg', index: 0 } },
    ])
    const cut2 = b.cut(stub)
    const a1 = b.atom(cut2, stub)
    const ns = b.termNode(cut2, p('SUCC y'))
    b.wire(cut2, [
      { node: a1, port: { kind: 'arg', index: 0 } },
      { node: ns, port: { kind: 'freeVar', name: 'y' } },
    ])
    const cut3 = b.cut(cut2)
    const a2 = b.atom(cut3, stub)
    b.wire(cut2, [
      { node: ns, port: { kind: 'output' } },
      { node: a2, port: { kind: 'arg', index: 0 } },
    ])
    const baseCl = mkDiagramWithBoundary(b.build(), [])

    push({ rule: 'insertion', region: rB, pattern: baseCl, attachments: [], binders: { [stub]: rB } })

    // find the spliced base atom + its zero wire in the CURRENT diagram
    const baseAtom = Object.entries(cur.nodes).find(([, n]) => n.kind === 'atom' && n.region === rB)![0]
    const w0Host = Object.entries(cur.wires).find(([, w]) =>
      w.endpoints.some((ep) => ep.node === baseAtom && ep.port.kind === 'arg'))![0]

    push({ rule: 'iteration', sel: mkSelection(cur, { region: rB, regions: [], nodes: [baseAtom], wires: [] }), target: cI })

    // 5': iterate the lhs ZERO node into rB sharing the boundary wire, then
    // join its copied output wire with the base's zero wire (inner = deeper
    // scope; rB is negative ✓)
    push({ rule: 'iteration', sel: mkSelection(cur, { region: cur.root, regions: [], nodes: [Object.keys(lhsDiagram.nodes)[0]!], wires: [] }), target: rB })
    // the copy's OUTPUT sits on the boundary wz (shared attachment) — the
    // base's zero wire w0Host is separate; join them (inner = deeper scope;
    // rB is negative, so the join is licensed):
    push({ rule: 'wireJoin', a: wz, b: w0Host })

    // capture the conclusion
    const rhs = mkDiagramWithBoundary(cur, [wz])
    const thm: Theorem = { name: 'zeroIsNat', lhs, rhs, steps }
    expect(() => checkTheorem(thm, ctx)).not.toThrow()
    // sanity on the captured shape: four atoms bound to the bubble (base,
    // two closure atoms, and the cut4 conclusion copy), boundary at root scope
    expect(Object.values(rhs.diagram.nodes).filter((n) => n.kind === 'atom')).toHaveLength(4)
    expect(rhs.diagram.wires[wz]!.scope).toBe(rhs.diagram.root)
  })
})
