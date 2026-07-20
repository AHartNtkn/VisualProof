export { ProofError } from './error'
export type { ProofContext, Theory } from './context'
export type { ProofStep } from './step'
export { applyStep, replayProof } from './step'
export {
  EMPTY_PROOF_CONTEXT, assertProofContext, extendRelations, registerTheorem, verifyTheory,
} from './context'
export type { PlacementHint, ProofAction } from './action'
export { singleStepAction, applyAction, replayActions } from './action'
export type { Theorem, TheoremApplication } from './theorem'
export { checkTheorem, applyTheorem } from './theorem'
export type { CompositionBoundaries, CompositionOptions } from './compose'
export { composeActions, mapStepIds } from './compose'
export {
  stepToJson, stepFromJson, theoremToJson, theoremFromJson, dwbToJson, dwbFromJson,
} from './json'
export { theoryToJson, theoryFromJson, loadTheory } from './store'
