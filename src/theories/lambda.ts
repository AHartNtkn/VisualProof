import { app, lam, bvar, freePorts, port, termEq, type Term } from '../kernel/term/term'
import { DiagramBuilder } from '../kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../kernel/diagram/boundary'
import { applyConversion } from '../kernel/rules/conversion'
import type { ProofStep } from '../kernel/proof/step'
import { EMPTY_PROOF_CONTEXT } from '../kernel/proof/context'
import { replayActions, singleStepAction } from '../kernel/proof/action'
import type { Theorem } from '../kernel/proof/theorem'
import type { Theory } from '../kernel/proof/store'
import type { Diagram } from '../kernel/diagram/diagram'
import { proposePortCorrespondence } from '../kernel/rules/port-correspondence'
import { termNodeAt } from '../kernel/rules/access'

// Pure λ demos: these theorems are ABOUT λ-terms, so the terms are the pure
// programs themselves (no named constants — named things are relation nodes).
const ONEp = lam(lam(app(bvar(1), bvar(0))))                           // λf x. f x
const TWOp = lam(lam(app(bvar(1), app(bvar(1), bvar(0)))))             // λf x. f (f x)
const PLUSp = lam(lam(lam(lam(app(app(bvar(3), bvar(1)), app(app(bvar(2), bvar(1)), bvar(0))))))) // λm n f x. m f (n f x)
const Yp = lam(app(lam(app(bvar(1), app(bvar(0), bvar(0)))), lam(app(bvar(1), app(bvar(0), bvar(0)))))) // λf. (λx. f (x x)) (λx. f (x x))

const ctx = EMPTY_PROOF_CONTEXT

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
  const actions = steps.map((step, index) => singleStepAction(`one plus one ${index + 1}`, step))
  let cur = replayActions(lhsDiagram, actions, ctx)
  const nodeWith = (t: Term): string => {
    const found = Object.entries(cur.nodes).find(([, nd]) => nd.kind === 'term' && termEq(nd.term, t))
    if (found === undefined) throw new Error('onePlusOne derivation: intro node not found')
    return found[0]
  }
  const a = nodeWith(poo)
  const b = nodeWith(TWOp)
  // harvest the 1+1 ~ 2 certificate once at build time (fuel-free replay)
  const scratch = new DiagramBuilder()
  const sn = scratch.termNode(scratch.root, poo)
  const scratchDiagram = scratch.build()
  const scratchNode = termNodeAt(scratchDiagram, sn)
  const correspondence = proposePortCorrespondence(scratchNode.term, TWOp, scratchNode.freePorts, freePorts(TWOp))
  const conv = applyConversion(scratchDiagram, sn, TWOp, correspondence, 4096)
  const join: ProofStep = { rule: 'congruenceJoin', a, b, certificate: conv.certificate, correspondence }
  steps.push(join)
  const joinAction = singleStepAction('join equal terms', join)
  actions.push(joinAction)
  cur = replayActions(cur, [joinAction], ctx)
  return { name: 'onePlusOne', lhs, rhs: mkDiagramWithBoundary(cur, []), actions }
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
    correspondence: proposePortCorrespondence(
      termNodeAt(lhsDiagram, n).term,
      newTerm,
      termNodeAt(lhsDiagram, n).freePorts,
      freePorts(newTerm),
    ),
    attachments: {},
  }
  const action = singleStepAction('unfold fixed point', step)
  const cur: Diagram = replayActions(lhsDiagram, [action], ctx)
  return { name: 'fixedPoint', lhs, rhs: mkDiagramWithBoundary(cur, [wo, wf]), actions: [action] }
}

export function buildLambdaTheory(): Theory {
  return {
    relations: [],
    theorems: [deriveOnePlusOne(), deriveFixedPoint()],
  }
}
