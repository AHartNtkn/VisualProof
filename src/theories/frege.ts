import { parseTerm } from '../kernel/term/parse'
import { app, port, type Term } from '../kernel/term/term'
import type { PathSeg } from '../kernel/term/reduce'
import { DiagramBuilder } from '../kernel/diagram/builder'
import { mkDiagramWithBoundary, type DiagramWithBoundary } from '../kernel/diagram/boundary'
import type { Diagram } from '../kernel/diagram/diagram'
import type { Definitions } from '../kernel/rules/definitions'
import { applyConversion } from '../kernel/rules/conversion'
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

/**
 * The general ℕ(x) — inCutNat. The base line w0 is scoped at the guard bubble
 * rB (NOT the root): the zero-witness lives strictly inside the cut, so ℕ is
 * non-vacuous (∃w0 is not witnessable outside the guard by a non-zero). The
 * boundary is the x-line, the only wire that leaves the cut.
 */
export function natRelation(): DiagramWithBoundary {
  const l = new DiagramBuilder()
  const cut1 = l.cut(l.root)
  const rB = l.bubble(cut1, 1)
  const nz = l.termNode(rB, p('ZERO'))
  const a0 = l.atom(rB, rB)
  // the base zero-line is scoped INSIDE the guard bubble (the non-vacuity fix)
  l.wire(rB, [
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

const PLUS_BODY = fregeDefinitions['PLUS']!

/**
 * A conversion (βη-only) theorem `o = start ⟹ o = target-refolded`, on a single
 * root term node whose output and free ports are the boundary. The recipe uses
 * canonical port names (s0, s1, …), which mkDiagram's name canonicalization
 * leaves fixed in first-occurrence order. Constants are opaque to β, so we
 * unfold before converting to the constant-free target, then refold. Built once
 * at load time; the recorded certificate makes replay fuel-free.
 */
type ConversionRecipe = {
  readonly name: string
  readonly start: string
  readonly freeVars: readonly string[]
  readonly unfolds: readonly (readonly PathSeg[])[]
  readonly target: Term
  readonly folds: readonly { readonly path: readonly PathSeg[]; readonly constId: string }[]
}

function deriveConversion(r: ConversionRecipe, ctx: ProofContext): Theorem {
  const l = new DiagramBuilder()
  const n = l.termNode(l.root, p(r.start))
  const wo = l.wire(l.root, [{ node: n, port: { kind: 'output' } }])
  const wf = r.freeVars.map((v) => l.wire(l.root, [{ node: n, port: { kind: 'freeVar', name: v } }]))
  const lhsDiagram = l.build()
  const lhs = mkDiagramWithBoundary(lhsDiagram, [wo, ...wf])

  let cur: Diagram = lhsDiagram
  const steps: ProofStep[] = []
  const push = (s: ProofStep): void => {
    steps.push(s)
    cur = replayProof(cur, [s], ctx)
  }
  for (const path of r.unfolds) push({ rule: 'unfold', node: n, path: [...path] })
  const conv = applyConversion(cur, n, r.target, 4096)
  push({ rule: 'conversion', node: n, term: r.target, certificate: conv.certificate, attachments: {} })
  for (const f of r.folds) push({ rule: 'fold', node: n, path: [...f.path], constId: f.constId })
  return { name: r.name, lhs, rhs: mkDiagramWithBoundary(cur, [wo, ...wf]), steps }
}

const conversionRecipes: readonly ConversionRecipe[] = [
  {
    name: 'plusAssoc',
    start: 'PLUS (PLUS s0 s1) s2',
    freeVars: ['s0', 's1', 's2'],
    unfolds: [['fn', 'fn'], ['fn', 'arg', 'fn', 'fn']],
    // the constant-free unfolded form of PLUS s0 (PLUS s1 s2)
    target: app(app(PLUS_BODY, port('s0')), app(app(PLUS_BODY, port('s1')), port('s2'))),
    folds: [{ path: ['arg', 'fn', 'fn'], constId: 'PLUS' }, { path: ['fn', 'fn'], constId: 'PLUS' }],
  },
  {
    name: 'plusLeftUnit',
    start: 'PLUS ZERO s0',
    freeVars: ['s0'],
    unfolds: [['fn', 'fn'], ['fn', 'arg']],
    target: port('s0'),
    folds: [],
  },
  {
    name: 'plusRightUnit',
    start: 'PLUS s0 ZERO',
    freeVars: ['s0'],
    unfolds: [['fn', 'fn'], ['arg']],
    target: port('s0'),
    folds: [],
  },
]

export function buildFregeTheory(): Theory {
  const relations = { nat: natRelation() }
  const ctx: ProofContext = {
    definitions: fregeDefinitions,
    theorems: new Map(),
    relations: new Map(Object.entries(relations)),
  }
  const theorems = conversionRecipes.map((r) => deriveConversion(r, ctx))
  return { definitions: fregeDefinitions, relations, theorems }
}
