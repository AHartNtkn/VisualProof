import { parseTerm } from '../kernel/term/parse'
import { app, port } from '../kernel/term/term'
import type { Term } from '../kernel/term/term'
import { DiagramBuilder } from '../kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../kernel/diagram/boundary'
import type { Definitions } from '../kernel/rules/definitions'
import { applyConversion } from '../kernel/rules/conversion'
import { replayProof, type ProofContext, type ProofStep } from '../kernel/proof/step'
import type { Theorem } from '../kernel/proof/theorem'
import type { Theory } from '../kernel/proof/store'
import type { Diagram } from '../kernel/diagram/diagram'

const consts = new Set(['ONE', 'TWO', 'PLUS', 'Y'])
const p = (s: string) => parseTerm(s, consts)
const noConsts = new Set<string>()
const pp = (s: string) => parseTerm(s, noConsts)

export const lambdaDefinitions: Definitions = {
  ONE: pp('\\f. \\x. f x'),
  TWO: pp('\\f. \\x. f (f x)'),
  PLUS: pp('\\m. \\n. \\f. \\x. m f (n f x)'),
  Y: pp('\\f. (\\x. f (x x)) (\\x. f (x x))'),
}

const ctx: ProofContext = { definitions: lambdaDefinitions, theorems: new Map() }

/** o = PLUS ONE ONE ⟹ o = TWO, by unfold → convert → fold. */
function deriveOnePlusOne(): Theorem {
  const l = new DiagramBuilder()
  const n = l.termNode(l.root, p('PLUS ONE ONE'))
  const wo = l.wire(l.root, [{ node: n, port: { kind: 'output' } }])
  const lhsDiagram = l.build()
  const lhs = mkDiagramWithBoundary(lhsDiagram, [wo])

  let cur: Diagram = lhsDiagram
  const steps: ProofStep[] = []
  const push = (s: ProofStep): void => {
    steps.push(s)
    cur = replayProof(cur, [s], ctx)
  }
  // t = app(app(PLUS, ONE), ONE): PLUS at ['fn','fn'], ONEs at ['fn','arg'], ['arg']
  push({ rule: 'unfold', node: n, path: ['fn', 'fn'] })
  push({ rule: 'unfold', node: n, path: ['fn', 'arg'] })
  push({ rule: 'unfold', node: n, path: ['arg'] })
  // interactive conversion ONCE at build time; the recorded step carries the
  // certificate, so replay (verifyTheory, loadTheory) is fuel-free
  const target: Term = lambdaDefinitions['TWO']!
  const conv = applyConversion(cur, n, target, 64)
  push({ rule: 'conversion', node: n, term: target, certificate: conv.certificate, attachments: {} })
  push({ rule: 'fold', node: n, path: [], constId: 'TWO' })
  return { name: 'onePlusOne', lhs, rhs: mkDiagramWithBoundary(cur, [wo]), steps }
}

/**
 * o = Y f ⟹ o = f (Y f). Both sides DIVERGE under normalization — the
 * fueled search can never bridge them. The hand-built certificate meets at
 * the common reduct f ((λx. f (x x)) (λx. f (x x))): two root betas on the
 * unfolded left, one arg beta on the partially-unfolded right (Church–Rosser
 * does the rest). The fold restores the constant on the right.
 */
function deriveFixedPoint(): Theorem {
  const l = new DiagramBuilder()
  const n = l.termNode(l.root, p('Y f'))
  const wo = l.wire(l.root, [{ node: n, port: { kind: 'output' } }])
  const wf = l.wire(l.root, [{ node: n, port: { kind: 'freeVar', name: 'f' } }])
  const lhsDiagram = l.build()
  const lhs = mkDiagramWithBoundary(lhsDiagram, [wo, wf])

  let cur: Diagram = lhsDiagram
  const steps: ProofStep[] = []
  const push = (s: ProofStep): void => {
    steps.push(s)
    cur = replayProof(cur, [s], ctx)
  }
  push({ rule: 'unfold', node: n, path: ['fn'] })
  // newTerm: f ((λf.body) f) — Y unfolded on the right so its redex can step
  const yBody = lambdaDefinitions['Y']!
  const newTerm: Term = app(port('f'), app(yBody, port('f')))
  push({
    rule: 'conversion', node: n, term: newTerm,
    certificate: {
      leftSteps: [{ kind: 'beta', path: [] }, { kind: 'beta', path: [] }],
      rightSteps: [{ kind: 'beta', path: ['arg'] }],
    },
    attachments: {},
  })
  push({ rule: 'fold', node: n, path: ['arg', 'fn'], constId: 'Y' })
  return { name: 'fixedPoint', lhs, rhs: mkDiagramWithBoundary(cur, [wo, wf]), steps }
}

export function buildLambdaTheory(): Theory {
  return {
    definitions: lambdaDefinitions,
    relations: {},
    theorems: [deriveOnePlusOne(), deriveFixedPoint()],
  }
}
