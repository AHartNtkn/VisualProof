// Plan 11 spike (conversion half): plusAssoc, plusLeftUnit, plusRightUnit as
// rewriting theorems in the fixedPoint shape, verified through checkTheorem.
import { parseTerm } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/term/parse'
import { app, port } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/term/term'
import type { Term } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/term/term'
import { DiagramBuilder } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/diagram/boundary'
import { applyConversion } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/rules/conversion'
import { replayProof, type ProofContext, type ProofStep } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/proof/step'
import { checkTheorem, type Theorem } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/proof/theorem'
import type { Diagram } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/diagram/diagram'
import { fregeDefinitions } from '/home/ahart/Documents/VisualProofAssistant/src/theories/frege'

const consts = new Set(['ZERO', 'SUCC', 'PLUS', 'ONE', 'TWO'])
const p = (s: string) => parseTerm(s, consts)
const ctx: ProofContext = { definitions: fregeDefinitions, theorems: new Map() }

type Recipe = {
  name: string
  start: string                 // node term for the lhs
  freeVars: string[]            // boundary lines besides the output
  unfolds: string[][]           // paths of constants to unfold, in order
  target: Term                  // constant-free conversion target (unfolded form)
  folds: { path: string[]; constId: string }[]
}

function derive(r: Recipe): Theorem {
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
    console.log(`  ${r.name}: ${s.rule} ok`)
  }
  for (const path of r.unfolds) push({ rule: 'unfold', node: n, path })
  // the conversion target must be the UNFOLDED form of r.target if folds follow;
  // build it by unfolding constants via parse-with-consts + explicit substitution:
  // simplest honest route: parse target with consts, then unfold the same way the
  // kernel does — replay fold AFTER converting to the fully-unfolded target.
  const conv = applyConversion(cur, n, r.target, 4096)
  push({ rule: 'conversion', node: n, term: r.target, certificate: conv.certificate, attachments: {} })
  for (const f of r.folds) push({ rule: 'fold', node: n, path: f.path, constId: f.constId })
  const thm: Theorem = { name: r.name, lhs, rhs: mkDiagramWithBoundary(cur, [wo, ...wf]), steps }
  checkTheorem(thm, ctx)
  console.log(`${r.name}: checkTheorem PASSED (${steps.length} steps)`)
  return thm
}

const PB = fregeDefinitions['PLUS']!
const recipes: Recipe[] = [
  {
    name: 'plusAssoc',
    start: 'PLUS (PLUS a b) c',
    freeVars: ['a', 'b', 'c'],
    unfolds: [['fn', 'fn'], ['fn', 'arg', 'fn', 'fn']],
    // unfolded form of PLUS a (PLUS b c)
    target: app(app(PB, port('a')), app(app(PB, port('b')), port('c'))),
    folds: [{ path: ['arg', 'fn', 'fn'], constId: 'PLUS' }, { path: ['fn', 'fn'], constId: 'PLUS' }],
  },
  {
    name: 'plusLeftUnit',
    start: 'PLUS ZERO n',
    freeVars: ['n'],
    unfolds: [['fn', 'fn'], ['fn', 'arg']],
    target: port('n'),
    folds: [],
  },
  {
    name: 'plusRightUnit',
    start: 'PLUS n ZERO',
    freeVars: ['n'],
    unfolds: [['fn', 'fn'], ['arg']],
    target: port('n'),
    folds: [],
  },
]

for (const r of recipes) {
  try {
    derive(r)
  } catch (e) {
    console.log(`${r.name}: FAILED — ${e instanceof Error ? e.message : String(e)}`)
  }
}
