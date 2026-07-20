import type { Term } from '../kernel/term/term'
import { freePorts } from '../kernel/term/term'
import type { ReductionStep } from '../kernel/term/reduce'
import type { ConversionCertificate } from '../kernel/term/certificate'
import { headNormalize, weakHeadNormalize } from '../kernel/term/hnf'
import type { Diagram, NodeId } from '../kernel/diagram/diagram'
import { termNodeAt } from '../kernel/rules/access'
import { applyConversionByCertificate } from '../kernel/rules/conversion'
import type { ProofStep } from '../kernel/proof/step'
import { proposePortCorrespondence } from '../kernel/rules/port-correspondence'

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
 * Shared finisher for the head-normalization tactics: refuse a no-op (the term
 * was already in the requested form), and otherwise apply the conversion with
 * the recorded head steps as the left half of the certificate. Head reduction
 * never adds free ports, so the attachments are empty.
 */
function applyHeadConversion(
  d: Diagram,
  node: NodeId,
  result: { readonly term: Term; readonly steps: readonly ReductionStep[] },
  formName: string,
): TacticResult {
  if (result.steps.length === 0) {
    throw new Error(`the term is already in ${formName}; refusing a no-op conversion step`)
  }
  const certificate: ConversionCertificate = { leftSteps: result.steps, rightSteps: [] }
  const source = termNodeAt(d, node)
  const correspondence = proposePortCorrespondence(source.term, result.term, source.freePorts, freePorts(result.term))
  const step: ProofStep = { rule: 'conversion', node, term: result.term, certificate, correspondence, attachments: {} }
  return { diagram: applyConversionByCertificate(d, node, result.term, certificate, correspondence, {}), step }
}

/** Head-normalize a term node (head β-steps only, descending under the binder prefix) and emit the conversion step. */
export function convertToHeadNormal(d: Diagram, node: NodeId, fuel: number): TacticResult {
  const r = headNormalize(termNodeAt(d, node).term, fuel)
  return applyHeadConversion(d, node, r, 'head-normal form')
}

/** Weak-head-normalize a term node and emit the conversion step. */
export function convertToWeakHeadNormal(d: Diagram, node: NodeId, fuel: number): TacticResult {
  const r = weakHeadNormalize(termNodeAt(d, node).term, fuel)
  return applyHeadConversion(d, node, r, 'weak head-normal form')
}
