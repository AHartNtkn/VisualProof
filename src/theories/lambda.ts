import { app, lam, bvar, port, type Term } from '../kernel/term/term'
import { DiagramBuilder } from '../kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../kernel/diagram/boundary'
import { applyConversion } from '../kernel/rules/conversion'
import { replayProof, type ProofContext, type ProofStep } from '../kernel/proof/step'
import type { Theorem } from '../kernel/proof/theorem'
import type { Theory } from '../kernel/proof/store'
import type { Diagram } from '../kernel/diagram/diagram'

// Pure λ demos: these theorems are ABOUT λ-terms, so the terms are the pure
// programs themselves (no named constants — named things are relation nodes).
const ONEp = lam(lam(app(bvar(1), bvar(0))))                           // λf x. f x
const TWOp = lam(lam(app(bvar(1), app(bvar(1), bvar(0)))))             // λf x. f (f x)
const PLUSp = lam(lam(lam(lam(app(app(bvar(3), bvar(1)), app(app(bvar(2), bvar(1)), bvar(0))))))) // λm n f x. m f (n f x)
const Yp = lam(app(lam(app(bvar(1), app(bvar(0), bvar(0)))), lam(app(bvar(1), app(bvar(0), bvar(0)))))) // λf. (λx. f (x x)) (λx. f (x x))

const ctx: ProofContext = { definitions: {}, theorems: new Map(), relations: new Map() }

/** o = (PLUS ONE ONE) ⟹ o = TWO, by a single recorded βη conversion. */
function deriveOnePlusOne(): Theorem {
  const l = new DiagramBuilder()
  const n = l.termNode(l.root, app(app(PLUSp, ONEp), ONEp))
  const wo = l.wire(l.root, [{ node: n, port: { kind: 'output' } }])
  const lhsDiagram = l.build()
  const lhs = mkDiagramWithBoundary(lhsDiagram, [wo])
  // interactive conversion ONCE at build time; the recorded step carries the
  // certificate, so replay (verifyTheory, loadTheory) is fuel-free
  const conv = applyConversion(lhsDiagram, n, TWOp, 4096)
  const step: ProofStep = { rule: 'conversion', node: n, term: TWOp, certificate: conv.certificate, attachments: {} }
  const cur = replayProof(lhsDiagram, [step], ctx)
  return { name: 'onePlusOne', lhs, rhs: mkDiagramWithBoundary(cur, [wo]), steps: [step] }
}

/**
 * o = Y f ⟹ o = f (Y f). Both sides DIVERGE under normalization — the fueled
 * search can never bridge them. The hand-built certificate meets at the common
 * reduct f ((λx. f (x x)) (λx. f (x x))): two root betas on the unfolded left,
 * one arg beta on the partially-unfolded right (Church–Rosser does the rest).
 */
function deriveFixedPoint(): Theorem {
  const l = new DiagramBuilder()
  const n = l.termNode(l.root, app(Yp, port('f')))
  const wo = l.wire(l.root, [{ node: n, port: { kind: 'output' } }])
  const wf = l.wire(l.root, [{ node: n, port: { kind: 'freeVar', name: 'f' } }])
  const lhsDiagram = l.build()
  const lhs = mkDiagramWithBoundary(lhsDiagram, [wo, wf])
  // the node's sole free port under its canonical post-construction name (s0)
  const newTerm: Term = app(port('s0'), app(Yp, port('s0')))
  const step: ProofStep = {
    rule: 'conversion', node: n, term: newTerm,
    certificate: {
      leftSteps: [{ kind: 'beta', path: [] }, { kind: 'beta', path: [] }],
      rightSteps: [{ kind: 'beta', path: ['arg'] }],
    },
    attachments: {},
  }
  const cur: Diagram = replayProof(lhsDiagram, [step], ctx)
  return { name: 'fixedPoint', lhs, rhs: mkDiagramWithBoundary(cur, [wo, wf]), steps: [step] }
}

export function buildLambdaTheory(): Theory {
  return {
    definitions: {},
    relations: {},
    theorems: [deriveOnePlusOne(), deriveFixedPoint()],
  }
}
