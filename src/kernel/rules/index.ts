export { RuleError } from './error'
export { applyWireJoin } from './wire-join'
export { applyRefSpawn, applyAtomSpawn } from './spawn'
export { applyErasure, applyWireSever } from './erasure'
export type { DeiterationEvidence, IdentityRetarget } from './iteration'
export {
  applyIteration,
  applyDeiteration,
  findDeiterationEvidence,
} from './iteration'
export type { IdentityContradictionEvidence } from './identity'
export {
  applyIdentityInsertion,
  applyIdentityContradiction,
} from './identity'
export { applyDoubleCutIntro, applyDoubleCutElim } from './doublecut'
export { applyUnfold, applyFold } from './fold'
export { applyVacuousIntro, applyVacuousElim } from './vacuous'
