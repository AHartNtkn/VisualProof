import type { Term } from '../kernel/term/term'
import type { ReductionStep } from '../kernel/term/reduce'
import type { ConversionCertificate } from '../kernel/term/certificate'
import { headNormalize, headSpine, weakHeadNormalize } from '../kernel/term/hnf'
import type { Diagram, NodeId } from '../kernel/diagram/diagram'
import { termNodeAt } from '../kernel/rules/access'
import { applyConversionByCertificate } from '../kernel/rules/conversion'
import type { ProofStep } from '../kernel/proof/step'

/**
 * Tactics: app-layer helpers that compute a rewrite and emit the ordinary
 * certificate-carrying ProofStep that justifies it. They add no trust — the
 * kernel re-checks the certificate on application and on every replay.
 */

export type TacticResult = {
  readonly diagram: Diagram
  readonly step: ProofStep
}

/**
 * Shared finisher for the head-normalization tactics: refuse a blocking
 * constant head (not rigid — headStrip would reject it; unfolding is the way
 * forward), refuse a no-op (the term was already in the requested form), and
 * otherwise apply the conversion with the recorded head steps as the left
 * half of the certificate. Head reduction never adds free ports, so the
 * attachments are empty.
 */
function applyHeadConversion(
  d: Diagram,
  node: NodeId,
  result: { readonly term: Term; readonly steps: readonly ReductionStep[] },
  blockingConst: string | undefined,
  formName: string,
): TacticResult {
  if (blockingConst !== undefined) {
    throw new Error(`head reduction stopped at the defined constant '${blockingConst}'; a defined constant head is not rigid — unfold it first`)
  }
  if (result.steps.length === 0) {
    throw new Error(`the term is already in ${formName}; refusing a no-op conversion step`)
  }
  const certificate: ConversionCertificate = { leftSteps: result.steps, rightSteps: [] }
  const step: ProofStep = { rule: 'conversion', node, term: result.term, certificate, attachments: {} }
  return { diagram: applyConversionByCertificate(d, node, result.term, certificate, {}), step }
}

/** Head-normalize a term node (head β-steps only, descending under the binder prefix) and emit the conversion step. */
export function convertToHeadNormal(d: Diagram, node: NodeId, fuel: number): TacticResult {
  const r = headNormalize(termNodeAt(d, node).term, fuel)
  const head = headSpine(r.term).head
  const blocking = head.kind === 'const' ? head.constId : undefined
  return applyHeadConversion(d, node, r, blocking, 'head-normal form')
}

/**
 * Weak-head-normalize a term node and emit the conversion step. A top-level
 * lambda IS weak head-normal, so a constant head under the binder prefix is
 * not a blocker here — only a constant at the spine head of a binder-free
 * result blocked the normalizer.
 */
export function convertToWeakHeadNormal(d: Diagram, node: NodeId, fuel: number): TacticResult {
  const r = weakHeadNormalize(termNodeAt(d, node).term, fuel)
  let blocking: string | undefined
  if (r.term.kind !== 'lam') {
    const head = headSpine(r.term).head
    if (head.kind === 'const') blocking = head.constId
  }
  return applyHeadConversion(d, node, r, blocking, 'weak head-normal form')
}
