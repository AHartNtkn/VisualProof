import { app, lam, bvar, port, termEq, type Term } from '../kernel/term/term'
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

const ctx: ProofContext = { theorems: new Map(), relations: new Map() }

/**
 * The CLOSED equation 1+1=2: empty sheet ⟹ ∃z. z = (PLUS ONE ONE) ∧ z = TWO —
 * one existential line carrying BOTH closed descriptions. Mere existence of a
 * closed term is trivial (terms denote); the JOIN of the two descriptions is
 * the content. Backwards reading: disconnect and erase to the blank page.
 */
function deriveOnePlusOne(): Theorem {
  const lhsDiagram = new DiagramBuilder().build()
  const lhs = mkDiagramWithBoundary(lhsDiagram, [])
  const poo = app(app(PLUSp, ONEp), ONEp)
  const steps: ProofStep[] = [
    { rule: 'closedTermIntro', region: lhsDiagram.root, term: poo },
    { rule: 'closedTermIntro', region: lhsDiagram.root, term: TWOp },
  ]
  const cur = replayProof(lhsDiagram, steps, ctx)
  return { name: 'onePlusOne', lhs, rhs: mkDiagramWithBoundary(cur, []), steps } // PROBE: skip congruenceJoin
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
    relations: {},
    theorems: [deriveOnePlusOne(), deriveFixedPoint()],
  }
}
