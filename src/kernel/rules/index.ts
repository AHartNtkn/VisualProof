export { RuleError } from './error'
export { applyWireJoin } from './wire-join'
export { applyOpenTermSpawn, applyRelationSpawn, applyBoundRelationSpawn } from './spawn'
export { applyErasure, applyWireSever } from './erasure'
export type { DeiterationEvidence } from './iteration'
export { applyIteration, applyDeiteration, findDeiterationEvidence } from './iteration'
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
export type { AbstractionOccurrence } from './comprehension'
export { applyComprehensionInstantiate, applyComprehensionAbstract } from './comprehension'
export { applyVacuousBubbleIntro, applyVacuousBubbleElim } from './vacuous'
