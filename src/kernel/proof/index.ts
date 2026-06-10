export { ProofError } from './error'
export type { ProofContext, ProofStep } from './step'
export { applyStep, replayProof } from './step'
export type { Theorem, TheoremApplication } from './theorem'
export { checkTheorem, applyTheorem } from './theorem'
export { composeProofs, mapStepIds } from './compose'
export {
  stepToJson, stepFromJson, theoremToJson, theoremFromJson, dwbToJson, dwbFromJson,
} from './json'
export type { Theory } from './store'
export { verifyTheory, theoryToJson, theoryFromJson, loadTheory } from './store'
