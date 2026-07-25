export { RuleError } from './error'
export { applyWireJoin } from './wire-join'
export { applyBodyAttach, applyBodyDetach } from './body'
export { applyOpenTermSpawn, applyRelationSpawn, applyBoundRelationSpawn } from './spawn'
export { applyErasure, applyWireSever } from './erasure'
export type { DeiterationEvidence, IdentityRetarget } from './iteration'
export { applyIteration, applyDeiteration, findDeiterationEvidence } from './iteration'
export type { IdentityContradictionEvidence } from './identity'
export { applyIdentityInsertion, applyIdentityContradiction } from './identity'
export { applyDoubleCutIntro, applyDoubleCutElim } from './doublecut'
export type { ConversionResult } from './conversion'
export { applyConversion, applyConversionByCertificate } from './conversion'
export type { PortCorrespondence } from './port-correspondence'
export {
  proposePortCorrespondence,
  validatePortCorrespondence,
  validatePortCorrespondenceCarrier,
} from './port-correspondence'
export { applyCongruenceJoin } from './congruence'
export {
  anchorAvailability,
  applyAnchoredWireSplit,
  applyAnchoredWireContract,
} from './anchored-wire'
export { applyHeadStrip } from './headstrip'
export { applyClosedTermIntro } from './intro'
export { applyFusion, applyFission } from './fusion'
export type { FoldTarget } from './fold'
export { applyUnfold, applyFold } from './fold'
export { applyVacuousIntro, applyVacuousElim } from './vacuous'
