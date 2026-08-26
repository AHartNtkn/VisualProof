import type { Diagram, NodeId } from '../kernel/diagram/diagram'
import type { ProofStep } from '../kernel/proof/step'
import {
  applyLambdaConversion,
  type SlotCorrespondence,
} from '../kernel/rules/lambda'
import { termNodeAt } from '../kernel/rules/access'
import type { ConversionCertificate } from '../kernel/term/certificate'
import { headNormalize, weakHeadNormalize } from '../kernel/term/hnf'
import { normalize, type ReductionStep } from '../kernel/term/reduce'
import type { Term } from '../kernel/term/term'

/** App-layer search output whose certificate is rechecked by the kernel. */
export type TacticResult = {
  readonly diagram: Diagram
  readonly step: ProofStep
}

function preservedInterface(freeArity: number): SlotCorrespondence {
  const slots = Array.from({ length: freeArity }, (_, slot) => slot)
  return {
    commonArity: freeArity,
    left: slots,
    right: [...slots],
  }
}

function finishConversion(
  diagram: Diagram,
  node: NodeId,
  term: Term,
  steps: readonly ReductionStep[],
  formName: string,
): TacticResult {
  if (steps.length === 0) {
    throw new Error(
      `the term is already in ${formName}; refusing a no-op conversion step`,
    )
  }
  const source = termNodeAt(diagram, node)
  const correspondence = preservedInterface(source.freeArity)
  const certificate: ConversionCertificate = {
    leftSteps: steps,
    rightSteps: [],
  }
  const step: ProofStep = {
    rule: 'lambdaConversion',
    node,
    term,
    correspondence,
    certificate,
    attachments: {},
  }
  return {
    diagram: applyLambdaConversion(
      diagram,
      node,
      term,
      correspondence,
      certificate,
    ),
    step,
  }
}

/** Fully beta-eta normalize one whole term under the interactive fuel budget. */
export function convertToNormal(
  diagram: Diagram,
  node: NodeId,
  fuel: number,
): TacticResult {
  const result = normalize(termNodeAt(diagram, node).term, fuel)
  if (result.status === 'fuel-exhausted') {
    throw new Error(
      `normalization exhausted its fuel of ${fuel} steps before reaching normal form`,
    )
  }
  return finishConversion(diagram, node, result.term, result.path, 'normal form')
}

/** Head beta-normalize through the leading binder prefix. */
export function convertToHeadNormal(
  diagram: Diagram,
  node: NodeId,
  fuel: number,
): TacticResult {
  const result = headNormalize(termNodeAt(diagram, node).term, fuel)
  return finishConversion(
    diagram,
    node,
    result.term,
    result.steps,
    'head-normal form',
  )
}

/** Beta-normalize only until the outer term reaches weak head-normal form. */
export function convertToWeakHeadNormal(
  diagram: Diagram,
  node: NodeId,
  fuel: number,
): TacticResult {
  const result = weakHeadNormalize(termNodeAt(diagram, node).term, fuel)
  return finishConversion(
    diagram,
    node,
    result.term,
    result.steps,
    'weak head-normal form',
  )
}
