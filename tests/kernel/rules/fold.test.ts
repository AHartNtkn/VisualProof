import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import type { Diagram, RegionId, WireId } from '../../../src/kernel/diagram/diagram'
import { mkDiagramWithBoundary, type DiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { relSig, IOTA, type RelSig } from '../../../src/kernel/diagram/sig'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { exploreForm } from '../../../src/kernel/diagram/canonical/explore'
import { applyBodyAttach } from '../../../src/kernel/rules/body'
import { applyUnfold, applyFold } from '../../../src/kernel/rules/fold'
import { RuleError } from '../../../src/kernel/rules/error'

const pc = (s: string) => parseTerm(s)
const R1: RelSig = relSig([IOTA])
const R2: RelSig = relSig([IOTA, IOTA])

// `resolve` for atom-flavor calls is never consulted: a body node supplies the content.
const noResolve = (_defId: string): DiagramWithBoundary | undefined => undefined

/* -------------------------------------------------------------------------- */
/* Body contents (DiagramWithBoundary): args-then-params boundary order.       */
/* -------------------------------------------------------------------------- */

/** Arity 1, no params: arg line `y` feeds a term node `tail` via freeVar `w`. */
function noParamBody(tail = 'C w'): DiagramWithBoundary {
  const b = new DiagramBuilder()
  const tA = b.termNode(b.root, pc('y'))
  const tB = b.termNode(b.root, pc(tail))
  b.wire(b.root, [
    { node: tA, port: { kind: 'output' } },
    { node: tB, port: { kind: 'freeVar', name: 'w' } },
  ], IOTA)
  const arg = b.wire(b.root, [{ node: tA, port: { kind: 'freeVar', name: 'y' } }], IOTA)
  return mkDiagramWithBoundary(b.build(), [arg])
}

/** Arity 1, one IOTA param: term node `(y w)`, arg line `y`, param line `w`. */
function termParamBody(): DiagramWithBoundary {
  const b = new DiagramBuilder()
  const t = b.termNode(b.root, pc('y w'))
  const arg = b.wire(b.root, [{ node: t, port: { kind: 'freeVar', name: 'y' } }], IOTA)
  const param = b.wire(b.root, [{ node: t, port: { kind: 'freeVar', name: 'w' } }], IOTA)
  return mkDiagramWithBoundary(b.build(), [arg, param])
}

/** Arity 2, no params: predicate `E x y`, boundary [x-line, y-line]. */
function binaryBody(): DiagramWithBoundary {
  const b = new DiagramBuilder()
  const t = b.termNode(b.root, pc('E x y'))
  const x = b.wire(b.root, [{ node: t, port: { kind: 'freeVar', name: 'x' } }], IOTA)
  const y = b.wire(b.root, [{ node: t, port: { kind: 'freeVar', name: 'y' } }], IOTA)
  return mkDiagramWithBoundary(b.build(), [x, y])
}

/** Arity 1, one RELATION param: an inner atom `S(y)` — head on the param line, arg on the arg line. */
function relParamBody(): DiagramWithBoundary {
  const b = new DiagramBuilder()
  const inner = b.atom(b.root, R1)
  const arg = b.wire(b.root, [{ node: inner, port: { kind: 'arg', index: 0 } }], IOTA)
  const param = b.wire(b.root, [{ node: inner, port: { kind: 'head' } }], R1)
  return mkDiagramWithBoundary(b.build(), [arg, param])
}

/* -------------------------------------------------------------------------- */
/* Host builders.                                                              */
/* -------------------------------------------------------------------------- */

/**
 * A relational wire W (sig `sig`) carrying a body (`content`, with host param
 * lines `params`) and an atom whose head is on W and whose args are `argWires`.
 * `region` places W (a cut = negative, so a forward attach fits; the root =
 * positive, needing a backward attach). Returns everything a test needs.
 */
type BodiedAtom = {
  d: Diagram
  atomId: string
  W: WireId
  argWires: WireId[]
  region: RegionId
  paramWires: WireId[]
}

function bodiedAtom(opts: {
  sig: RelSig
  content: DiagramWithBoundary
  negative: boolean
  paramSpec?: readonly ('term' | 'rel')[]
  diagonal?: boolean
}): BodiedAtom {
  const b = new DiagramBuilder()
  const region = opts.negative ? b.cut(b.root) : b.root
  const atomId = b.atom(region, opts.sig)
  const W = b.wire(region, [{ node: atomId, port: { kind: 'head' } }], opts.sig)
  const argWires: WireId[] = []
  const argCount = opts.sig.args.length
  if (opts.diagonal) {
    const carrier = b.termNode(region, pc('a'))
    const shared = b.wire(region, [
      { node: atomId, port: { kind: 'arg', index: 0 } },
      { node: atomId, port: { kind: 'arg', index: 1 } },
      { node: carrier, port: { kind: 'freeVar', name: 'a' } },
    ], IOTA)
    argWires.push(shared, shared)
  } else {
    for (let i = 0; i < argCount; i++) {
      const carrier = b.termNode(region, pc(`a${i}`))
      const aw = b.wire(region, [
        { node: atomId, port: { kind: 'arg', index: i } },
        { node: carrier, port: { kind: 'freeVar', name: `a${i}` } },
      ], IOTA)
      argWires.push(aw)
    }
  }
  // Param host lines live at root (at-or-outside W's scope in both cases).
  const paramWires: WireId[] = []
  const specs = opts.paramSpec ?? []
  specs.forEach((kind, j) => {
    if (kind === 'term') {
      const pc0 = b.termNode(b.root, pc(`p${j}`))
      paramWires.push(b.wire(b.root, [{ node: pc0, port: { kind: 'freeVar', name: `p${j}` } }], IOTA))
    } else {
      paramWires.push(b.relWire(b.root, R1))
    }
  })
  const base = b.build()
  const d = applyBodyAttach(base, W, opts.content, paramWires, opts.negative ? 'forward' : 'backward')
  return { d, atomId, W, argWires, region, paramWires }
}

/** A ref of `defId`/`sig` in `region` with each arg-i on a fresh carrier line. */
function refHost(defId: string, sig: RelSig, inCut = false) {
  const b = new DiagramBuilder()
  const region = inCut ? b.cut(b.root) : b.root
  const node = b.ref(region, defId, sig)
  const argWires: WireId[] = []
  sig.args.forEach((_, i) => {
    const carrier = b.termNode(region, pc(`a${i}`))
    argWires.push(b.wire(region, [
      { node, port: { kind: 'arg', index: i } },
      { node: carrier, port: { kind: 'freeVar', name: `a${i}` } },
    ], IOTA))
  })
  return { d: b.build(), node, argWires, region }
}

/** Selection of exactly `nodes` (all directly in `region`) with their internal wires. */
function occFrom(d: Diagram, nodes: string[], region: RegionId) {
  const set = new Set(nodes)
  const internal = Object.keys(d.wires).filter((wid) => {
    const w = d.wires[wid]!
    return w.scope === region && w.endpoints.length > 0 && w.endpoints.every((ep) => set.has(ep.node))
  })
  return mkSelection(d, { region, regions: [], nodes, wires: internal })
}

/** Node ids present in `after` but not in `before` — the freshly spliced copy. */
function freshNodes(before: Diagram, after: Diagram): string[] {
  return Object.keys(after.nodes).filter((id) => !(id in before.nodes))
}

/* -------------------------------------------------------------------------- */
/* Unfold — bodied atoms.                                                       */
/* -------------------------------------------------------------------------- */

describe('unfold: a bodied atom inlines the body and drops the atom (polarity-free)', () => {
  for (const negative of [true, false]) {
    it(`unfolds at a ${negative ? 'negative' : 'positive'} scope, leaving the body node in place`, () => {
      const { d, atomId, W, region } = bodiedAtom({ sig: R1, content: noParamBody(), negative })
      const un = applyUnfold(d, atomId, noResolve)

      expect(un.nodes[atomId]).toBeUndefined()
      // the body node on W survives (the definition is not consumed by one unfold)
      const bodyStill = W in un.wires &&
        un.wires[W]!.endpoints.some((ep) => ep.port.kind === 'output' && un.nodes[ep.node]?.kind === 'body')
      expect(bodyStill).toBe(true)
      // two term nodes of the body were spliced into the atom's region
      const fresh = freshNodes(d, un).filter((id) => un.nodes[id]!.region === region)
      expect(fresh.length).toBe(2)
      expect(fresh.every((id) => un.nodes[id]!.kind === 'term')).toBe(true)
    })
  }
})

describe('unfold: parameters land on the body node param lines', () => {
  it('splices the param stub onto the very wire feeding the body freeVar port', () => {
    const { d, atomId, argWires, paramWires, region } = bodiedAtom({
      sig: R1, content: termParamBody(), negative: true, paramSpec: ['term'],
    })
    const un = applyUnfold(d, atomId, noResolve)
    const [copied] = freshNodes(d, un).filter((id) => un.nodes[id]!.region === region)
    expect(copied).toBeDefined()
    // the copied `(y w)` node has its y-freeVar on the arg wire and w-freeVar on the param wire
    const onArg = un.wires[argWires[0]!]!.endpoints.some((ep) => ep.node === copied && ep.port.kind === 'freeVar')
    const onParam = un.wires[paramWires[0]!]!.endpoints.some((ep) => ep.node === copied && ep.port.kind === 'freeVar')
    expect(onArg).toBe(true)
    expect(onParam).toBe(true)
  })
})

describe('unfold: a diagonal atom R(x,x) lands both arg stubs on one wire', () => {
  it('merges both boundary positions onto the shared arg wire', () => {
    const { d, atomId, argWires, region } = bodiedAtom({
      sig: R2, content: binaryBody(), negative: true, diagonal: true,
    })
    const shared = argWires[0]!
    const un = applyUnfold(d, atomId, noResolve)
    const [copied] = freshNodes(d, un).filter((id) => un.nodes[id]!.region === region)
    // the copied `E x y` node carries BOTH its x and y freeVar ports on the one shared wire
    const freeVarEps = un.wires[shared]!.endpoints.filter((ep) => ep.node === copied && ep.port.kind === 'freeVar')
    expect(freeVarEps.length).toBe(2)
  })
})

describe('unfold: refuses an atom whose head wire carries no body', () => {
  it('throws naming the atom', () => {
    const b = new DiagramBuilder()
    const atomId = b.atom(b.root, R1)
    b.wire(b.root, [{ node: atomId, port: { kind: 'head' } }], R1) // bare relational wire, no body
    const carrier = b.termNode(b.root, pc('a'))
    b.wire(b.root, [
      { node: atomId, port: { kind: 'arg', index: 0 } },
      { node: carrier, port: { kind: 'freeVar', name: 'a' } },
    ], IOTA)
    const d = b.build()
    expect(() => applyUnfold(d, atomId, noResolve)).toThrow(RuleError)
    expect(() => applyUnfold(d, atomId, noResolve)).toThrow(/head wire carries no body to unfold/)
  })
})

/* -------------------------------------------------------------------------- */
/* Unfold — named refs (absorbed from the old relation-definition rule).        */
/* -------------------------------------------------------------------------- */

describe('unfold: a named ref inlines its resolved body and drops the ref', () => {
  it('inlines onto arg-0 and removes the reference', () => {
    const resolve = (id: string) => (id === 'R' ? noParamBody() : undefined)
    const { d, node, argWires } = refHost('R', R1)
    const un = applyUnfold(d, node, resolve)
    expect(un.nodes[node]).toBeUndefined()
    expect(Object.values(un.nodes).filter((n) => n.kind === 'ref')).toHaveLength(0)
    const landed = un.wires[argWires[0]!]!.endpoints.filter((ep) => un.nodes[ep.node]?.kind === 'term' && ep.port.kind === 'freeVar')
    expect(landed.length).toBeGreaterThanOrEqual(1)
  })

  it('refuses an unresolvable defId', () => {
    const { d, node } = refHost('R', R1)
    expect(() => applyUnfold(d, node, noResolve)).toThrow(/no relation named 'R'/)
  })

  it('refuses when the ref sig arity disagrees with the body boundary length', () => {
    const resolve = (id: string) => (id === 'R' ? noParamBody() : undefined) // arity 1 body
    const { d, node } = refHost('R', R2) // ref claims arity 2
    expect(() => applyUnfold(d, node, resolve)).toThrow(/arity 2 but relation 'R' has 1/)
  })

  it('refuses a node that is neither atom nor ref', () => {
    const b = new DiagramBuilder()
    const t = b.termNode(b.root, pc('a'))
    const d = b.build()
    expect(() => applyUnfold(d, t, (id) => (id === 'R' ? noParamBody() : undefined)))
      .toThrow(/atom or ref/)
  })
})

/* -------------------------------------------------------------------------- */
/* Fold — round-trips and refusals.                                             */
/* -------------------------------------------------------------------------- */

describe('fold: round-trips unfold for a bodied atom', () => {
  it('re-forms the exact diagram (canonical equality) after unfold then fold', () => {
    const { d, atomId, W, argWires, region } = bodiedAtom({ sig: R1, content: noParamBody(), negative: true })
    const un = applyUnfold(d, atomId, noResolve)
    const sel = occFrom(un, freshNodes(d, un).filter((id) => un.nodes[id]!.region === region), region)
    const folded = applyFold(un, sel, [argWires[0]!], { wireId: W })
    expect(exploreForm(folded)).toBe(exploreForm(d))
  })

  it('round-trips a param body: params come from the target wire body, not the caller', () => {
    const { d, atomId, W, argWires, region } = bodiedAtom({
      sig: R1, content: termParamBody(), negative: true, paramSpec: ['term'],
    })
    const un = applyUnfold(d, atomId, noResolve)
    const sel = occFrom(un, freshNodes(d, un).filter((id) => un.nodes[id]!.region === region), region)
    const folded = applyFold(un, sel, [argWires[0]!], { wireId: W })
    expect(exploreForm(folded)).toBe(exploreForm(d))
  })

  it('round-trips at a positive scope', () => {
    const { d, atomId, W, argWires, region } = bodiedAtom({
      sig: R1, content: termParamBody(), negative: false, paramSpec: ['term'],
    })
    const un = applyUnfold(d, atomId, noResolve)
    const sel = occFrom(un, freshNodes(d, un).filter((id) => un.nodes[id]!.region === region), region)
    const folded = applyFold(un, sel, [argWires[0]!], { wireId: W })
    expect(exploreForm(folded)).toBe(exploreForm(d))
  })
})

describe('fold: argument order is load-bearing (asymmetric multi-arg body)', () => {
  it('round-trips with correct arg order, refuses transposed args (fingerprint mismatch)', () => {
    // binaryBody = E x y, structurally asymmetric under arg swap.
    const { d, atomId, W, argWires, region } = bodiedAtom({ sig: R2, content: binaryBody(), negative: true })
    const [a0, a1] = [argWires[0]!, argWires[1]!]
    const un = applyUnfold(d, atomId, noResolve)
    const nodes = freshNodes(d, un).filter((id) => un.nodes[id]!.region === region)

    const folded = applyFold(un, occFrom(un, nodes, region), [a0, a1], { wireId: W })
    expect(exploreForm(folded)).toBe(exploreForm(d))

    // Transposed args pin the occurrence against the body in the wrong order: E x y
    // does not equal E y x, so the boundary-pinned canonical forms differ.
    expect(() => applyFold(un, occFrom(un, nodes, region), [a1, a0], { wireId: W })).toThrow(RuleError)
    expect(() => applyFold(un, occFrom(un, nodes, region), [a1, a0], { wireId: W })).toThrow(/does not match/)
  })
})

describe('fold: a diagonal occurrence round-trips with repeated args', () => {
  it('unfolds R(x,x) then folds back with args [w, w] to the exact diagram', () => {
    const { d, atomId, W, argWires, region } = bodiedAtom({
      sig: R2, content: binaryBody(), negative: true, diagonal: true,
    })
    const shared = argWires[0]!
    const un = applyUnfold(d, atomId, noResolve)
    const nodes = freshNodes(d, un).filter((id) => un.nodes[id]!.region === region)
    const folded = applyFold(un, occFrom(un, nodes, region), [shared, shared], { wireId: W })
    expect(exploreForm(folded)).toBe(exploreForm(d))
  })
})

describe('fold: refuses a target wire with no body to fold against', () => {
  it('throws when the target wire is bare', () => {
    // Unfold a bodied atom, then remove the body by folding onto a DIFFERENT bare wire.
    const { d, atomId, argWires, region } = bodiedAtom({ sig: R1, content: noParamBody(), negative: true })
    const un = applyUnfold(d, atomId, noResolve)
    const sel = occFrom(un, freshNodes(d, un).filter((id) => un.nodes[id]!.region === region), region)
    // Target a wire that exists but carries no body node: the atom's arg wire.
    expect(() => applyFold(un, sel, [argWires[0]!], { wireId: argWires[0]! })).toThrow(RuleError)
    expect(() => applyFold(un, sel, [argWires[0]!], { wireId: argWires[0]! })).toThrow(/carries no body/)
  })
})

describe('fold: refuses a fingerprint mismatch', () => {
  it('a near-miss occurrence (one node changed) does not fold', () => {
    // Body of the target wire is `C w`; the occurrence is inlined from `w w`.
    const { d, atomId, W, argWires, region } = bodiedAtom({ sig: R1, content: noParamBody('w w'), negative: true })
    const un = applyUnfold(d, atomId, noResolve)
    // Re-attach a DIFFERENT body (`C w`) onto W so the fold target disagrees with the occurrence.
    // W already carries `w w`; detach is not available here, so instead target a wire whose
    // body is `C w` by building a parallel host. Simpler: fold the `w w` occurrence but
    // compare against a `C w` body via a ref target.
    const sel = occFrom(un, freshNodes(d, un).filter((id) => un.nodes[id]!.region === region), region)
    void W
    const resolve = (id: string) => (id === 'R' ? noParamBody('C w') : undefined)
    expect(() => applyFold(un, sel, [argWires[0]!], { defId: 'R', sig: R1, resolve })).toThrow(RuleError)
    expect(() => applyFold(un, sel, [argWires[0]!], { defId: 'R', sig: R1, resolve })).toThrow(/does not match/)
  })
})

describe('fold: named ref target round-trips', () => {
  it('folds an inlined body back to the exact ref diagram', () => {
    const resolve = (id: string) => (id === 'R' ? noParamBody() : undefined)
    const { d, node, argWires, region } = refHost('R', R1)
    const un = applyUnfold(d, node, resolve)
    const sel = occFrom(un, freshNodes(d, un).filter((id) => un.nodes[id]!.region === region), region)
    const folded = applyFold(un, sel, [argWires[0]!], { defId: 'R', sig: R1, resolve })
    expect(exploreForm(folded)).toBe(exploreForm(d))
  })

  it('mints exactly one fresh node — the reference — against the pre-removal id set', () => {
    const resolve = (id: string) => (id === 'R' ? noParamBody() : undefined)
    const { d, node, argWires, region } = refHost('R', R1)
    const un = applyUnfold(d, node, resolve)
    const sel = occFrom(un, freshNodes(d, un).filter((id) => un.nodes[id]!.region === region), region)
    const folded = applyFold(un, sel, [argWires[0]!], { defId: 'R', sig: R1, resolve })
    const fresh = Object.keys(folded.nodes).filter((id) => un.nodes[id] === undefined)
    expect(fresh.length).toBe(1)
    expect(folded.nodes[fresh[0]!]!.kind).toBe('ref')
  })

  it('identical bodies under different names give DISTINCT refs (fold is defId-directed)', () => {
    const resolve = (id: string) => ((id === 'R1n' || id === 'R2n') ? noParamBody() : undefined)
    const { d, node, argWires, region } = refHost('R1n', R1)
    const un = applyUnfold(d, node, resolve)
    const nodes = freshNodes(d, un).filter((id) => un.nodes[id]!.region === region)
    const asR1 = applyFold(un, occFrom(un, nodes, region), [argWires[0]!], { defId: 'R1n', sig: R1, resolve })
    const asR2 = applyFold(un, occFrom(un, nodes, region), [argWires[0]!], { defId: 'R2n', sig: R1, resolve })
    expect(exploreForm(asR1)).not.toBe(exploreForm(asR2))
    expect(exploreForm(asR1)).toBe(exploreForm(d))
  })

  it('refuses a repeated arg that leaves a distinct crossing wire unused', () => {
    // Arity-2 body S(x,y) = two disconnected conjuncts, one boundary each.
    const bodyS = (): DiagramWithBoundary => {
      const b = new DiagramBuilder()
      const tx = b.termNode(b.root, pc('x'))
      const ty = b.termNode(b.root, pc('y'))
      const bx = b.wire(b.root, [{ node: tx, port: { kind: 'freeVar', name: 'x' } }], IOTA)
      const by = b.wire(b.root, [{ node: ty, port: { kind: 'freeVar', name: 'y' } }], IOTA)
      return mkDiagramWithBoundary(b.build(), [bx, by])
    }
    const resolve = (id: string) => (id === 'S' ? bodyS() : undefined)
    const { d, node, argWires, region } = refHost('S', R2)
    const un = applyUnfold(d, node, resolve)
    const nodes = freshNodes(d, un).filter((id) => un.nodes[id]!.region === region)
    const sel = occFrom(un, nodes, region)
    expect(() => applyFold(un, sel, [argWires[0]!, argWires[1]!], { defId: 'S', sig: R2, resolve })).not.toThrow()
    expect(() => applyFold(un, sel, [argWires[0]!, argWires[0]!], { defId: 'S', sig: R2, resolve }))
      .toThrow(/is not used by any argument position/)
  })
})

/* -------------------------------------------------------------------------- */
/* Fold — occurrences that reference an outer relation wire (externally bound).  */
/* -------------------------------------------------------------------------- */

describe('fold: an occurrence referencing an outer relation param wire', () => {
  it('folds a rel-param body back to the atom (param corresponds to the outer wire)', () => {
    const { d, atomId, W, argWires, region } = bodiedAtom({
      sig: R1, content: relParamBody(), negative: true, paramSpec: ['rel'],
    })
    const un = applyUnfold(d, atomId, noResolve)
    // the copied inner atom's head sits on the OUTER param relation wire, outside the occurrence
    const nodes = freshNodes(d, un).filter((id) => un.nodes[id]!.region === region)
    const sel = occFrom(un, nodes, region)
    const folded = applyFold(un, sel, [argWires[0]!], { wireId: W })
    expect(exploreForm(folded)).toBe(exploreForm(d))
  })

  it('refuses when the arg/param correspondence is wrong (fingerprint mismatch)', () => {
    const { d, atomId, W, argWires, region } = bodiedAtom({
      sig: R1, content: relParamBody(), negative: true, paramSpec: ['rel'],
    })
    const un = applyUnfold(d, atomId, noResolve)
    const nodes = freshNodes(d, un).filter((id) => un.nodes[id]!.region === region)
    const sel = occFrom(un, nodes, region)
    // Fold against a term-param body: the occurrence's rel-param stub cannot match a term arg body.
    const resolve = (id: string) => (id === 'T' ? termParamBody() : undefined)
    void W
    expect(() => applyFold(un, sel, [argWires[0]!], { defId: 'T', sig: R1, resolve })).toThrow(RuleError)
  })
})
