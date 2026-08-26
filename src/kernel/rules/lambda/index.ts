export type { SlotCorrespondence } from './correspondence'
export {
  mapTermToCommonCarrier,
  validateSlotCorrespondence,
  validateSlotCorrespondenceCarrier,
} from './correspondence'
export { applyLambdaConversion } from './conversion'
export type { FreeVariableIdentityAction } from './free-variable-identity'
export { applyFreeVariableIdentity } from './free-variable-identity'
export type { LambdaSpawnOrientation } from './spawn'
export { applyLambdaTermSpawn } from './spawn'
export { applyLambdaFission, applyLambdaFusion } from './fission'
export { applyLambdaCongruenceJoin } from './congruence'
export { applyLambdaHeadStrip } from './head-strip'
export {
  anchorAvailability,
  applyLambdaAnchoredWireContract,
  applyLambdaAnchoredWireSplit,
} from './anchored-wire'
