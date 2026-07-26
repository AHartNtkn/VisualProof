export { ProofError } from './error'
export type { ProofContext, Theory } from './context'
export type {
  ProofStep,
  StepReceipt,
  WireInterfaceTransport,
  WireProvenance,
} from './step'
export {
  applyStep,
  applyStepWithReceipt,
  replayProof,
  transportBoundary,
} from './step'
export {
  EMPTY_PROOF_CONTEXT, assertProofContext, extendRelations, registerTheorem, verifyTheory,
} from './context'
export type {
  ActionReceipt,
  PlacementHint,
  ProofAction,
  ProofAllocation,
} from './action'
export {
  applyAction,
  applyActionWithReceipt,
  replayActions,
  singleStepAction,
} from './action'
export type { Theorem, TheoremApplication } from './theorem'
export { checkTheorem, applyTheorem } from './theorem'
export type { CompositionBoundaries, CompositionOptions } from './compose'
export { composeActions, mapStepIds } from './compose'
export {
  stepToJson, stepFromJson, theoremToJson, theoremFromJson,
} from './json'
export { theoryToJson, theoryFromJson, loadTheory } from './store'
