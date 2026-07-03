import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import type { Diagram, RegionId } from '../../../src/kernel/diagram/diagram'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import type { DiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { exploreForm } from '../../../src/kernel/diagram/canonical/explore'
import { applyRelUnfold, applyRelFold } from '../../../src/kernel/rules/reldef'

/**
 * Plan 11e Task 5 review battery: independent soundness probes beyond the
 * mandated mutation set. Each targets a specific claim in the plan's Part B.
 */

const pc = (s: string) => parseTerm(s)

/** Arity-1 body identical to reldef.test's bodyR: `y`-line boundary feeding `C w`. */
function bodyR(): DiagramWithBoundary {
  const b = new DiagramBuilder()
  const tA = b.termNode(b.root, pc('y'))
  const tB = b.termNode(b.root, pc('C w'))
  b.wire(b.root, [
    { node: tA, port: { kind: 'output' } },
    { node: tB, port: { kind: 'freeVar', name: 'w' } },
  ])
  const bound = b.wire(b.root, [{ node: tA, port: { kind: 'freeVar', name: 'y' } }])
  return mkDiagramWithBoundary(b.build(), [bound])
}

/** Arity-2 body S(x,y): two disconnected conjuncts, one boundary line each. */
function bodyS(): DiagramWithBoundary {
  const b = new DiagramBuilder()
  const tx = b.termNode(b.root, pc('x'))
  const ty = b.termNode(b.root, pc('y'))
  const bx = b.wire(b.root, [{ node: tx, port: { kind: 'freeVar', name: 'x' } }])
  const by = b.wire(b.root, [{ node: ty, port: { kind: 'freeVar', name: 'y' } }])
  return mkDiagramWithBoundary(b.build(), [bx, by])
}

/** A single ref node of `defId`/arity-1 whose arg-0 is wired to a carrier `a`. */
function refHost1(defId: string) {
  const b = new DiagramBuilder()
  const node = b.ref(b.root, defId, 1)
  const carrier = b.termNode(b.root, pc('a'))
  const wArg = b.wire(b.root, [
    { node, port: { kind: 'arg', index: 0 } },
    { node: carrier, port: { kind: 'freeVar', name: 'a' } },
  ])
  return { d: b.build(), node, carrier, wArg, region: b.root }
}

/** A ref of `defId`/arity-2, arg-i wired to carrier i. */
function refHost2(defId: string) {
  const b = new DiagramBuilder()
  const node = b.ref(b.root, defId, 2)
  const c0 = b.termNode(b.root, pc('a'))
  const c1 = b.termNode(b.root, pc('b'))
  const w0 = b.wire(b.root, [
    { node, port: { kind: 'arg', index: 0 } },
    { node: c0, port: { kind: 'freeVar', name: 'a' } },
  ])
  const w1 = b.wire(b.root, [
    { node, port: { kind: 'arg', index: 1 } },
    { node: c1, port: { kind: 'freeVar', name: 'b' } },
  ])
  return { d: b.build(), node, c0, c1, w0, w1, region: b.root }
}

/** Everything except the given carriers, plus the wires internal to that content. */
function bodySelectionExcluding(d: Diagram, carriers: Set<string>, region: RegionId) {
  const bodyNodes = Object.keys(d.nodes).filter((id) => !carriers.has(id))
  const bset = new Set(bodyNodes)
  const internal = Object.keys(d.wires).filter((wid) => {
    const eps = d.wires[wid]!.endpoints
    return eps.length > 0 && eps.every((ep) => bset.has(ep.node)) && d.wires[wid]!.scope === region
  })
  return mkSelection(d, { region, regions: [], nodes: bodyNodes, wires: internal })
}

describe('canonical key injectivity — adversarial colon-bearing defIds', () => {
  // The content key `ref:${defId}:${arity}` is compared as a whole string, never
  // parsed. Injectivity of (defId, arity) → key therefore reduces to string
  // equality; because arity always renders as a non-empty digit run, the last
  // colon is an unambiguous separator, so no distinct pair can collide. The
  // adversarial `a:1` / `a` pair — the one a naive last-colon split might blur —
  // must produce different fingerprints.
  const fp = (defId: string) => exploreForm(refHost1(defId).d)

  it('a defId containing a colon does not collide with its prefix', () => {
    expect(fp('a:1')).not.toBe(fp('a'))
    expect(fp('a:1')).not.toBe(fp('a:2'))
    expect(fp('a')).not.toBe(fp('b'))
  })
})

describe('fold is defId-directed — no ref is canonicalized by its body', () => {
  it('identical bodies under different names give DISTINCT refs; fold names its target', () => {
    // R1 and R2 are byte-identical bodies. The same inlined material folds under
    // either name, but the two refs are distinct diagrams — the ref is keyed by
    // defId, never by the body — so R2(a) is a different statement than R1(a).
    // This is SOUND: identical bodies denote the same relation, so R1(a) ⟺ R2(a)
    // as a definitional equivalence; naming R2 forges nothing.
    const relations = new Map([['R1', bodyR()], ['R2', bodyR()]])
    const { d, node, carrier, wArg, region } = refHost1('R1')
    const un = applyRelUnfold(d, node, relations)
    const sel = bodySelectionExcluding(un, new Set([carrier]), region)

    const asR1 = applyRelFold(un, sel, 'R1', [wArg], relations)
    const asR2 = applyRelFold(un, sel, 'R2', [wArg], relations)

    expect(exploreForm(asR1)).not.toBe(exploreForm(asR2))
    // folding back under the original name reproduces the original ref diagram
    expect(exploreForm(asR1)).toBe(exploreForm(d))
  })
})

describe('relFold args discipline — the diagonal is refused', () => {
  it('folding with a repeated argument wire is refused (distinctness gate)', () => {
    const relations = new Map([['S', bodyS()]])
    const { d, node, c0, c1, w0, w1, region } = refHost2('S')
    const un = applyRelUnfold(d, node, relations)
    const sel = bodySelectionExcluding(un, new Set([c0, c1]), region)

    // the honest fold with two distinct arg wires is accepted
    expect(() => applyRelFold(un, sel, 'S', [w0, w1], relations)).not.toThrow()
    // the diagonal (one host wire as both args) is refused before any fingerprint work
    expect(() => applyRelFold(un, sel, 'S', [w0, w0], relations)).toThrow(/not distinct/)
  })
})

describe('Task 2b soundness — a stored top-level bubble unfolds to valid ∃-content', () => {
  it('an "open-looking" body (bubble baked in as if a stub) unfolds to a closed, valid diagram', () => {
    // Sharpest case: a body authored to LOOK like an extractSubgraph of an open
    // pattern — a top-level bubble binding an atom whose arg is the boundary,
    // exactly the shape a would-be external-binder stub has. relUnfold splices
    // with an EMPTY binder map, so the bubble is copied as content: a genuine ∃.
    // The result is a well-formed diagram (mkDiagram inside splice would throw
    // otherwise) in which the atom is bound by the copied bubble — it cannot
    // escape. No forgery: the outcome is a sound, closed statement, merely weaker
    // than any "open" intent the author might have imagined (which was never
    // stored). We observe the diagram is valid and the atom stays bound.
    const b = new DiagramBuilder()
    const bub = b.bubble(b.root, 1)
    const at = b.atom(bub, bub)
    const bound = b.wire(b.root, [{ node: at, port: { kind: 'arg', index: 0 } }])
    const existsBody = mkDiagramWithBoundary(b.build(), [bound])
    const relations = new Map([['E', existsBody]])

    const { d, node } = refHost1('E')
    const un = applyRelUnfold(d, node, relations) // throws if the result is ill-formed

    const bubbles = Object.entries(un.regions).filter(([, r]) => r.kind === 'bubble')
    expect(bubbles).toHaveLength(1)
    const copiedBubble = bubbles[0]![0]
    const boundAtoms = Object.values(un.nodes).filter((n) => n.kind === 'atom' && n.binder === copiedBubble)
    expect(boundAtoms).toHaveLength(1) // the atom is bound by the copied ∃-bubble, not free
  })
})
