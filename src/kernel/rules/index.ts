export { RuleError } from './error'
export { applyInsertion, applyWireJoin } from './insertion'
export { applyErasure, applyWireSever } from './erasure'
export { applyIteration, applyDeiteration } from './iteration'
export { applyDoubleCutIntro, applyDoubleCutElim } from './doublecut'
export type { ConversionResult } from './conversion'
export { applyConversion, applyConversionByCertificate } from './conversion'
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
