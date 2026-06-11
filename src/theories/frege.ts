import { parseTerm } from '../kernel/term/parse'
import { DiagramBuilder } from '../kernel/diagram/builder'
import type { Diagram, NodeId, RegionId, WireId } from '../kernel/diagram/diagram'
import { mkDiagramWithBoundary, type DiagramWithBoundary } from '../kernel/diagram/boundary'
import { mkSelection } from '../kernel/diagram/subgraph/selection'
import type { Definitions } from '../kernel/rules/definitions'
import { replayProof, type ProofContext, type ProofStep } from '../kernel/proof/step'
import type { Theorem } from '../kernel/proof/theorem'
import type { Theory } from '../kernel/proof/store'

const consts = new Set(['ZERO', 'SUCC', 'PLUS', 'ONE', 'TWO'])
const p = (s: string) => parseTerm(s, consts)
const noConsts = new Set<string>()
const pp = (s: string) => parseTerm(s, noConsts)

export const fregeDefinitions: Definitions = {
  ZERO: pp('\\f. \\x. x'),
  ONE: pp('\\f. \\x. f x'),
  TWO: pp('\\f. \\x. f (f x)'),
  SUCC: pp('\\n. \\f. \\x. f (n f x)'),
  PLUS: pp('\\m. \\n. \\f. \\x. m f (n f x)'),
}

/** The general ℕ(x): separate zero-line, boundary = the x-line. */
export function natRelation(): DiagramWithBoundary {
  const l = new DiagramBuilder()
  const cut1 = l.cut(l.root)
  const rB = l.bubble(cut1, 1)
  const nz = l.termNode(rB, p('ZERO'))
  const a0 = l.atom(rB, rB)
  // the canonical general ℕ: the base zero-line is ROOT-scoped
  l.wire(l.root, [
    { node: nz, port: { kind: 'output' } },
    { node: a0, port: { kind: 'arg', index: 0 } },
  ])
  const cut2 = l.cut(rB)
  const a1 = l.atom(cut2, rB)
  const ny = l.termNode(cut2, p('SUCC y'))
  l.wire(cut2, [
    { node: a1, port: { kind: 'arg', index: 0 } },
    { node: ny, port: { kind: 'freeVar', name: 'y' } },
  ])
  const cut3 = l.cut(cut2)
  const a2 = l.atom(cut3, rB)
  l.wire(cut2, [
    { node: ny, port: { kind: 'output' } },
    { node: a2, port: { kind: 'arg', index: 0 } },
  ])
  const cut4 = l.cut(rB)
  const a3 = l.atom(cut4, rB)
  const wx = l.wire(l.root, [{ node: a3, port: { kind: 'arg', index: 0 } }])
  return mkDiagramWithBoundary(l.build(), [wx])
}

/**
 * The base+closure open pattern with the zero-line as a BOUNDARY: insertion
 * attaches it to the host's base line, so deiterations of base copies find
 * this base as their justifier with matching attachments. Used by succNat.
 */
function baseClAttached() {
  const b = new DiagramBuilder()
  const stub = b.bubble(b.root, 1)
  const bz = b.termNode(stub, p('ZERO'))
  const a0 = b.atom(stub, stub)
  const w0stub = b.wire(b.root, [
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
  return { pattern: mkDiagramWithBoundary(b.build(), [w0stub]), stub }
}

/**
 * The same base+closure open pattern with an INTERNAL zero-line: insertion
 * gives the base its own bubble-scoped line, severed to root scope afterwards.
 * Used by zeroIsNat, whose lhs has no pre-existing base line to attach to.
 */
function baseClOwned() {
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
  return { pattern: mkDiagramWithBoundary(b.build(), []), stub }
}

/** The open comp "x : R′(x)". */
function rPrimeComp() {
  const b = new DiagramBuilder()
  const stub = b.bubble(b.root, 1)
  const atom = b.atom(stub, stub)
  const bx = b.wire(b.root, [{ node: atom, port: { kind: 'arg', index: 0 } }])
  return { comp: mkDiagramWithBoundary(b.build(), [bx]), stub }
}

/** zeroIsNat: z = ZERO ⟹ z = ZERO ∧ ℕ(z), targeting the canonical general ℕ. */
function deriveZeroIsNat(ctx: ProofContext): Theorem {
  // ---- lhs: a single ZERO node whose output is the boundary wire
  const l = new DiagramBuilder()
  const nz = l.termNode(l.root, p('ZERO'))
  const wz = l.wire(l.root, [{ node: nz, port: { kind: 'output' } }])
  const lhsDiagram = l.build()
  const lhs = mkDiagramWithBoundary(lhsDiagram, [wz])

  let cur: Diagram = lhsDiagram
  const steps: ProofStep[] = []
  const push = (s: ProofStep): void => {
    steps.push(s)
    cur = replayProof(cur, [s], ctx)
  }

  // ---- ℕ-intro skeleton (steps 1–3)
  push({ rule: 'doubleCutIntro', sel: mkSelection(cur, { region: cur.root, regions: [], nodes: [], wires: [] }) })
  const cO = Object.entries(cur.regions).find(
    ([id, r]) => r.kind === 'cut' && r.parent === cur.root && lhsDiagram.regions[id] === undefined,
  )![0]
  const cI = Object.entries(cur.regions).find(
    ([, r]) => r.kind === 'cut' && r.parent === cO,
  )![0]

  push({ rule: 'vacuousIntro', sel: mkSelection(cur, { region: cO, regions: [cI], nodes: [], wires: [] }), arity: 1 })
  const rBp = Object.entries(cur.regions).find(([, r]) => r.kind === 'bubble')![0]

  // open-insert the OWNED variant: base′ gets its own rB′-scoped zero-line w0′
  const { pattern: baseCl, stub: bcStub } = baseClOwned()
  push({ rule: 'insertion', region: rBp, pattern: baseCl, attachments: [], binders: { [bcStub]: rBp } })
  const baseAtom = Object.entries(cur.nodes).find(
    ([, n]) => n.kind === 'atom' && n.region === rBp,
  )![0]
  const w0p = Object.entries(cur.wires).find(([, w]) =>
    w.endpoints.some((ep) => ep.node === baseAtom && ep.port.kind === 'arg'))![0]

  // ---- step 4: open-iterate the base atom into cI → conclusion copy A3 on w0′
  push({ rule: 'iteration', sel: mkSelection(cur, { region: rBp, regions: [], nodes: [baseAtom], wires: [] }), target: cI })
  const a3 = Object.entries(cur.nodes).find(
    ([, n]) => n.kind === 'atom' && n.region === cI,
  )![0]

  // ---- step 5: identify the boundary z with the base individual.
  // inner = w0′ scoped at rB′ (negative ✓); the merged wire keeps the OUTER id wz.
  push({ rule: 'wireJoin', a: wz, b: w0p })

  // ---- step 6: sever the base back onto its own ROOT-scoped line — the
  // canonical general ℕ keeps the base zero separate from the x-line. Kept on
  // wz: the lhs evidence and the conclusion atom; moved: base ZERO′ + A0′.
  push({
    rule: 'wireSever',
    wire: wz,
    keep: [
      { node: nz, port: { kind: 'output' } },
      { node: a3, port: { kind: 'arg', index: 0 } },
    ],
  })

  return { name: 'zeroIsNat', lhs, rhs: mkDiagramWithBoundary(cur, [wz]), steps }
}

/** succNat: ℕ(n) ∧ m = SUCC n ⟹ m = SUCC n ∧ ℕ(m) — the 16-step derivation. */
function deriveSuccNat(ctx: ProofContext): Theorem {
  // ---- lhs: SUCC evidence at root + the general ℕ(n) (separate zero-line)
  const l = new DiagramBuilder()
  const nS = l.termNode(l.root, p('SUCC y'))
  const cut1 = l.cut(l.root)
  const rB = l.bubble(cut1, 1)
  const nz = l.termNode(rB, p('ZERO'))
  const a0 = l.atom(rB, rB)
  // the canonical general ℕ: the base zero-line is ROOT-scoped — the form
  // zeroIsNat derives and theorem composition (oneIsNat) matches against
  const w0 = l.wire(l.root, [
    { node: nz, port: { kind: 'output' } },
    { node: a0, port: { kind: 'arg', index: 0 } },
  ])
  const cut2 = l.cut(rB)
  const a1 = l.atom(cut2, rB)
  const ny = l.termNode(cut2, p('SUCC y'))
  l.wire(cut2, [
    { node: a1, port: { kind: 'arg', index: 0 } },
    { node: ny, port: { kind: 'freeVar', name: 'y' } },
  ])
  const cut3 = l.cut(cut2)
  const a2 = l.atom(cut3, rB)
  l.wire(cut2, [
    { node: ny, port: { kind: 'output' } },
    { node: a2, port: { kind: 'arg', index: 0 } },
  ])
  const cut4 = l.cut(rB)
  const a3 = l.atom(cut4, rB)
  const wn = l.wire(l.root, [
    { node: nS, port: { kind: 'freeVar', name: 'y' } },
    { node: a3, port: { kind: 'arg', index: 0 } },
  ])
  const wm = l.wire(l.root, [{ node: nS, port: { kind: 'output' } }])
  const lhsDiagram = l.build()
  const lhs = mkDiagramWithBoundary(lhsDiagram, [wn, wm])

  let cur: Diagram = lhsDiagram
  const steps: ProofStep[] = []
  const push = (s: ProofStep): void => {
    steps.push(s)
    cur = replayProof(cur, [s], ctx)
  }
  const newCutIn = (parent: RegionId, before: Diagram): RegionId =>
    Object.entries(cur.regions).find(
      ([id, r]) => r.kind === 'cut' && r.parent === parent && before.regions[id] === undefined,
    )![0]
  const atomsIn = (region: RegionId): [NodeId, { kind: 'atom'; region: RegionId; binder: RegionId }][] =>
    Object.entries(cur.nodes).filter(
      (e): e is [NodeId, { kind: 'atom'; region: RegionId; binder: RegionId }] =>
        e[1].kind === 'atom' && e[1].region === region,
    )
  const wireOf = (node: NodeId, key: 'arg' | 'output' | 'freeVar'): WireId =>
    Object.entries(cur.wires).find(([, w]) =>
      w.endpoints.some((ep) => ep.node === node && ep.port.kind === key))![0]

  // ---- ℕ-intro skeleton (steps 1–3)
  let snapshot = cur
  push({ rule: 'doubleCutIntro', sel: mkSelection(cur, { region: cur.root, regions: [], nodes: [], wires: [] }) })
  const cO = newCutIn(cur.root, snapshot)
  const cI = newCutIn(cO, snapshot)

  push({ rule: 'vacuousIntro', sel: mkSelection(cur, { region: cO, regions: [cI], nodes: [], wires: [] }), arity: 1 })
  const rBp = Object.entries(cur.regions).find(
    ([id, r]) => r.kind === 'bubble' && lhsDiagram.regions[id] === undefined,
  )![0]

  const { pattern: baseCl, stub: bcStub } = baseClAttached()
  // the inserted base shares the lhs ℕ's base line w0, so base-copy
  // deiterations later find it with matching attachments
  push({ rule: 'insertion', region: rBp, pattern: baseCl, attachments: [w0], binders: { [bcStub]: rBp } })
  // the ambient closure cut inside rB′: its child cut OTHER than cI
  // (vacuousIntro reparented cI into the bubble)
  const cut2p = Object.entries(cur.regions).find(
    ([id, r]) => r.kind === 'cut' && r.parent === rBp && id !== cI,
  )![0]

  // ---- induction application (steps 4–8): R′(n) materializes in cI
  snapshot = cur
  push({ rule: 'iteration', sel: mkSelection(cur, { region: cur.root, regions: [cut1], nodes: [], wires: [] }), target: cI })
  const cut1c = newCutIn(cI, snapshot)
  const rBc = Object.entries(cur.regions).find(
    ([, r]) => r.kind === 'bubble' && r.parent === cut1c,
  )![0]

  const { comp: xRp, stub: xStub } = rPrimeComp()
  push({ rule: 'comprehensionInstantiate', bubble: rBc, comp: xRp, binders: { [xStub]: rBp } })
  // after dissolution, cut1c holds: ZEROc + its R′-atom (the base copy),
  // the closure copy cut2c, and the conclusion copy cut4c
  const zeroC = Object.entries(cur.nodes).find(
    ([, n]) => n.kind === 'term' && n.region === cut1c,
  )![0]
  // the copy's base sits ON the shared root-scoped w0 (an attachment, not
  // an internal wire) — its deiteration is justified by the inserted base′
  const baseAtomC = atomsIn(cut1c).find(([id]) => wireOf(id, 'arg') === w0)![0]
  push({
    rule: 'deiteration',
    sel: mkSelection(cur, { region: cut1c, regions: [], nodes: [zeroC, baseAtomC], wires: [] }),
    fuel: 64,
  })

  // the closure copy: the child of cut1c that itself has a child cut
  const cut2c = Object.entries(cur.regions).find(
    ([id, r]) => r.kind === 'cut' && r.parent === cut1c &&
      Object.values(cur.regions).some((rr) => rr.kind === 'cut' && rr.parent === id),
  )![0]
  push({ rule: 'deiteration', sel: mkSelection(cur, { region: cut1c, regions: [cut2c], nodes: [], wires: [] }), fuel: 64 })

  push({ rule: 'doubleCutElim', region: cut1c })
  // R′(n): the atom now in cI on the wn line
  const rPrimeN = atomsIn(cI).find(([id]) => wireOf(id, 'arg') === wn)![0]

  // ---- guarded modus ponens (steps 9–14): R′(m) materializes in cI
  snapshot = cur
  push({ rule: 'iteration', sel: mkSelection(cur, { region: rBp, regions: [cut2p], nodes: [], wires: [] }), target: cI })
  const cut2c2 = newCutIn(cI, snapshot)
  const hypAtom = atomsIn(cut2c2)[0]![0]
  const wyC2 = wireOf(hypAtom, 'arg')
  push({ rule: 'wireJoin', a: wn, b: wyC2 })
  push({ rule: 'deiteration', sel: mkSelection(cur, { region: cut2c2, regions: [], nodes: [hypAtom], wires: [] }), fuel: 64 })
  const succC2 = Object.entries(cur.nodes).find(
    ([, n]) => n.kind === 'term' && n.region === cut2c2,
  )![0]
  const wsC2 = wireOf(succC2, 'output')
  push({ rule: 'wireJoin', a: wm, b: wsC2 })
  push({ rule: 'deiteration', sel: mkSelection(cur, { region: cut2c2, regions: [], nodes: [succC2], wires: [] }), fuel: 64 })
  push({ rule: 'doubleCutElim', region: cut2c2 })

  // ---- cleanup (steps 15–16)
  push({ rule: 'erasure', sel: mkSelection(cur, { region: cI, regions: [], nodes: [rPrimeN], wires: [] }) })
  push({ rule: 'erasure', sel: mkSelection(cur, { region: cur.root, regions: [cut1], nodes: [], wires: [] }) })

  return { name: 'succNat', lhs, rhs: mkDiagramWithBoundary(cur, [wn, wm]), steps }
}

/** oneIsNat: z = ZERO ∧ o = SUCC z ⟹ ℕ(o) — two native theorem applications. */
function deriveOneIsNat(zeroIsNat: Theorem, succNat: Theorem, ctx: ProofContext): Theorem {
  const l = new DiagramBuilder()
  const nz = l.termNode(l.root, p('ZERO'))
  const nS = l.termNode(l.root, p('SUCC y'))
  const wz = l.wire(l.root, [
    { node: nz, port: { kind: 'output' } },
    { node: nS, port: { kind: 'freeVar', name: 'y' } },
  ])
  const wo = l.wire(l.root, [{ node: nS, port: { kind: 'output' } }])
  const lhsDiagram = l.build()
  const lhs = mkDiagramWithBoundary(lhsDiagram, [wo])

  let cur: Diagram = lhsDiagram
  const steps: ProofStep[] = []
  const push = (s: ProofStep): void => {
    steps.push(s)
    cur = replayProof(cur, [s], ctx)
  }
  // 1: cite zeroIsNat forward at the ZERO node (root is positive)
  push({
    rule: 'theorem', name: zeroIsNat.name, direction: 'forward',
    at: { sel: mkSelection(cur, { region: cur.root, regions: [], nodes: [nz], wires: [] }), args: [wz] },
  })
  // the rewrite replaced the ZERO node with zeroIsNat's rhs: ZERO evidence
  // back on wz plus the ℕ-shape cut and its root-scoped base line; find them
  const cut1 = Object.entries(cur.regions).find(
    ([, r]) => r.kind === 'cut' && r.parent === cur.root,
  )![0]
  const w0Image = Object.entries(cur.wires).find(
    ([id, w]) => w.scope === cur.root && id !== wz && id !== wo,
  )![0]
  // 2: cite succNat forward at { ℕ(z) ∧ o = SUCC z }. The base line must be
  // an EXPLICIT selected wire — root-scoped wires are boundary unless listed,
  // and succNat.lhs holds its base line as internal. The ZERO-evidence node
  // on wz stays OUTSIDE the selection (context).
  push({
    rule: 'theorem', name: succNat.name, direction: 'forward',
    at: {
      sel: mkSelection(cur, { region: cur.root, regions: [cut1], nodes: [nS], wires: [w0Image] }),
      args: [wz, wo],
    },
  })
  return { name: 'oneIsNat', lhs, rhs: mkDiagramWithBoundary(cur, [wo]), steps }
}

export function buildFregeTheory(): Theory {
  const ctx0: ProofContext = { definitions: fregeDefinitions, theorems: new Map() }
  const zeroIsNat = deriveZeroIsNat(ctx0)
  const succNat = deriveSuccNat(ctx0)
  const ctx1: ProofContext = {
    definitions: fregeDefinitions,
    theorems: new Map([[zeroIsNat.name, zeroIsNat], [succNat.name, succNat]]),
  }
  const oneIsNat = deriveOneIsNat(zeroIsNat, succNat, ctx1)
  return {
    definitions: fregeDefinitions,
    relations: { nat: natRelation() },
    theorems: [zeroIsNat, succNat, oneIsNat],
  }
}
