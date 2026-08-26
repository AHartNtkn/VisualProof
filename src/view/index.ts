export type { Vec2 } from './vec'
export { vec, add, sub, scale, length, polar } from './vec'
export type { NodeGeometry, NodeArc, NodeRadial, TermOccurrenceGeometry, TermOccurrenceHit } from './bend'
export { atomGeometry, bendGrid, bendMaps, refGeometry, identityGeometry, termGeometry, GAP_ANGLE } from './bend'
export type { Bar, GridOccurrence, GridOccurrenceHit, Rail, Stem, TrompGrid } from './tromp'
export { trompGrid } from './tromp'
export type { Body, BodyKind, Engine, Leg, LegEnd, RegionCircle } from './engine'
export {
  mkEngine, worldAnchor, portNormal, pkey, nodeGeometry, anchorOf, ascaleOf, frameBounds, frameSlots,
  localToWorld, isBodyObstacle, DISC_R, FRAME_MARGIN,
} from './engine'
export { settle, settleStep, recomputeRegions, resolveOverlaps, REGION_PAD, SIB_GAP } from './relax'
export type { LegGeom } from './wires'
export { computeLegs, legPaths } from './wires'
export type { Theme, Shape } from './paint'
export { paint, relationWireHues, highlightGroup, nextTheme, LIGHT, DARK, THEMES } from './paint'
