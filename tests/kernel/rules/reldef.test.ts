import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import type { Diagram, RegionId, WireId } from '../../../src/kernel/diagram/diagram'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import type { DiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { exploreForm } from '../../../src/kernel/diagram/canonical/explore'
import { applyRelUnfold, applyRelFold } from '../../../src/kernel/rules/reldef'
import { RuleError } from '../../../src/kernel/rules/error'
import { replayProof } from '../../../src/kernel/proof/step'
import type { ProofContext, ProofStep } from '../../../src/kernel/proof/step'
import { stepToJson, stepFromJson } from '../../../src/kernel/proof/json'

const pc = (s: string) => parseTerm(s)

/**
 * A self-contained arity-1 relation body: a term node `y` whose y-input is the
 * argument line (the boundary) and whose output feeds a second term node `C w`.
 * `tail` picks the second node's term so a near-miss body ('D w') can differ by
 * exactly one node.
 */
function bodyR(tail = 'C w'): DiagramWithBoundary {
  const b = new DiagramBuilder()
  const tA = b.termNode(b.root, pc('y'))
  const tB = b.termNode(b.root, pc(tail))
  b.wire(b.root, [
    { node: tA, port: { kind: 'output' } },
    { node: tB, port: { kind: 'freeVar', name: 'w' } },
  ])
  const bound = b.wire(b.root, [{ node: tA, port: { kind: 'freeVar', name: 'y' } }])
  return mkDiagramWithBoundary(b.build(), [bound])
}

/** A ref of `defId`/`arity` in `region`, arg-0 wired to a carrier term node. */
function refHost(defId: string, arity = 1, region?: (b: DiagramBuilder) => RegionId) {
  const b = new DiagramBuilder()
  const r = region ? region(b) : b.root
  const node = b.ref(r, defId, arity)
  const carrier = b.termNode(r, pc('a'))
  const wArg = b.wire(r, [
    { node, port: { kind: 'arg', index: 0 } },
    { node: carrier, port: { kind: 'freeVar', name: 'a' } },
  ])
  return { d: b.build(), node, carrier, wArg, region: r }
}

/** Body-content nodes of an unfolded host: everything except the carrier. */
function bodySelection(d: Diagram, carrier: string, region: RegionId) {
  const bodyNodes = Object.keys(d.nodes).filter((id) => id !== carrier)
  const bodyNodeSet = new Set(bodyNodes)
  const internal = Object.keys(d.wires).filter((wid) => {
    const eps = d.wires[wid]!.endpoints
    return eps.length > 0 && eps.every((ep) => bodyNodeSet.has(ep.node)) && d.wires[wid]!.scope === region
  })
  return mkSelection(d, { region, regions: [], nodes: bodyNodes, wires: internal })
}

describe('relUnfold — the body lands on the arg wire and the ref is removed', () => {
  it('inlines the relation body onto arg-0 and drops the reference', () => {
    const relations = new Map([['R', bodyR()]])
    const { d, node, carrier, wArg } = refHost('R')
    const un = applyRelUnfold(d, node, relations)

    expect(un.nodes[node]).toBeUndefined()
    expect(Object.values(un.nodes).filter((n) => n.kind === 'ref')).toHaveLength(0)
    // ref + carrier (2) becomes carrier + two body nodes (3)
    expect(Object.keys(un.nodes)).toHaveLength(3)
    // the body's argument line merged onto wArg: exactly one non-carrier endpoint, on a term node
    const argWire = un.wires[wArg]
    expect(argWire).toBeDefined()
    const landed = argWire!.endpoints.filter((ep) => ep.node !== carrier)
    expect(landed).toHaveLength(1)
    expect(un.nodes[landed[0]!.node]?.kind).toBe('term')
  })
})

describe('relFold — round-trips to fingerprint equality with the original reference', () => {
  it('folds the inlined body back to the exact reference diagram', () => {
    const relations = new Map([['R', bodyR()]])
    const { d, node, carrier, wArg } = refHost('R')
    const un = applyRelUnfold(d, node, relations)
    const sel = bodySelection(un, carrier, un.root)
    const folded = applyRelFold(un, sel, 'R', [wArg], relations)
    expect(exploreForm(folded)).toBe(exploreForm(d))
  })
})

describe('relUnfold — refusals', () => {
  it('refuses an unknown defId', () => {
    const { d, node } = refHost('R')
    expect(() => applyRelUnfold(d, node, new Map())).toThrow(RuleError)
    expect(() => applyRelUnfold(d, node, new Map())).toThrow(/no relation named 'R'/)
  })

  it('refuses when the reference arity disagrees with the body boundary length', () => {
    const relations = new Map([['R', bodyR()]]) // arity 1
    const { d, node } = refHost('R', 2) // ref claims arity 2
    expect(() => applyRelUnfold(d, node, relations)).toThrow(/arity 2 but relation 'R' has 1/)
  })

  it('refuses a non-reference node', () => {
    const b = new DiagramBuilder()
    const t = b.termNode(b.root, pc('a'))
    const d = b.build()
    expect(() => applyRelUnfold(d, t, new Map([['R', bodyR()]]))).toThrow(/reference nodes/)
  })
})

describe('relFold — refuses a near-miss body (one node changed)', () => {
  it('refuses to fold a structurally different body as the R-relation (fingerprint mismatch)', () => {
    // R's tail node is the bare arg `w`; RD's tail applies it to itself `w w` —
    // a one-node structural change the canonical fingerprint must distinguish.
    const relations = new Map([['R', bodyR('w')], ['RD', bodyR('w w')]])
    const { d, node, carrier, wArg } = refHost('RD')
    const un = applyRelUnfold(d, node, relations) // inlines the RD-body
    const sel = bodySelection(un, carrier, un.root)
    expect(() => applyRelFold(un, sel, 'R', [wArg], relations)).toThrow(RuleError)
    expect(() => applyRelFold(un, sel, 'R', [wArg], relations)).toThrow(/does not match relation 'R'/)
  })
})

/** R(x) := ∃S[S(x)]: a top-level bubble binding one atom whose arg is the boundary. */
function existsBody(): DiagramWithBoundary {
  const b = new DiagramBuilder()
  const bub = b.bubble(b.root, 1)
  const at = b.atom(bub, bub)
  const bound = b.wire(b.root, [{ node: at, port: { kind: 'arg', index: 0 } }])
  return mkDiagramWithBoundary(b.build(), [bound])
}

describe('relUnfold / relFold on a body with a top-level bubble (closed by construction)', () => {
  it('copies the body bubble as fresh content and folds back to fingerprint equality', () => {
    const relations = new Map([['E', existsBody()]])
    const { d, node, carrier, wArg, region } = refHost('E')
    const un = applyRelUnfold(d, node, relations)
    expect(un.nodes[node]).toBeUndefined()
    // the ∃-bubble was copied as a fresh region binding one fresh atom
    const bubbles = Object.entries(un.regions).filter(([, r]) => r.kind === 'bubble')
    expect(bubbles).toHaveLength(1)
    const bubId = bubbles[0]![0]
    const atoms = Object.values(un.nodes).filter((n) => n.kind === 'atom' && n.binder === bubId)
    expect(atoms).toHaveLength(1)
    void carrier
    // fold the copied ∃-subtree back to the reference
    const sel = mkSelection(un, { region, regions: [bubId], nodes: [], wires: [] })
    const folded = applyRelFold(un, sel, 'E', [wArg], relations)
    expect(exploreForm(folded)).toBe(exploreForm(d))
  })
})

describe('relUnfold / relFold are polarity-blind (work inside a cut)', () => {
  it('unfolds a ref inside a cut and folds it back', () => {
    const relations = new Map([['R', bodyR()]])
    const { d, node, carrier, wArg, region } = refHost('R', 1, (b) => b.cut(b.root))
    const un = applyRelUnfold(d, node, relations)
    expect(un.nodes[node]).toBeUndefined()
    expect(Object.values(un.nodes).filter((n) => n.kind === 'ref')).toHaveLength(0)
    const sel = bodySelection(un, carrier, region)
    const folded = applyRelFold(un, sel, 'R', [wArg], relations)
    expect(exploreForm(folded)).toBe(exploreForm(d))
  })
})

describe('relUnfold / relFold replay through applyStep', () => {
  it('replays a relUnfold step to the same diagram as the direct applier', () => {
    const relations = new Map([['R', bodyR()]])
    const { d, node } = refHost('R')
    const ctx: ProofContext = { theorems: new Map(), relations }
    const replayed = replayProof(d, [{ rule: 'relUnfold', node }], ctx)
    expect(exploreForm(replayed)).toBe(exploreForm(applyRelUnfold(d, node, relations)))
  })

  it('replays unfold then fold back to the original', () => {
    const relations = new Map([['R', bodyR()]])
    const { d, node, carrier, wArg } = refHost('R')
    const ctx: ProofContext = { theorems: new Map(), relations }
    const un = applyRelUnfold(d, node, relations)
    const sel = bodySelection(un, carrier, un.root)
    const steps: ProofStep[] = [
      { rule: 'relUnfold', node },
      { rule: 'relFold', sel, defId: 'R', args: [wArg] },
    ]
    const out = replayProof(d, steps, ctx)
    expect(exploreForm(out)).toBe(exploreForm(d))
  })
})

describe('relUnfold / relFold steps survive JSON round-trip', () => {
  it('serializes and parses both rules', () => {
    const sel = { region: 'r0', regions: [] as RegionId[], nodes: [] as string[], wires: [] as WireId[] }
    const unfold: ProofStep = { rule: 'relUnfold', node: 'n0' }
    const fold: ProofStep = { rule: 'relFold', sel, defId: 'R', args: ['w0'] }
    expect(stepFromJson(JSON.parse(JSON.stringify(stepToJson(unfold))))).toEqual(unfold)
    expect(stepFromJson(JSON.parse(JSON.stringify(stepToJson(fold))))).toEqual(fold)
  })
})
