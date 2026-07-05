export type { Vec2 } from './vec'
export { vec, add, sub, scale, length, polar } from './vec'
export type { TrompGrid, Bar, Stem, Rail } from './tromp'
export { trompGrid } from './tromp'
export type { NodeGeometry, NodeArc, NodeRadial } from './bend'
export { bendGrid, atomGeometry, GAP_ANGLE } from './bend'
export type { Body, BodyKind, Engine, Leg, LegEnd, RegionCircle } from './engine'
export {
  mkEngine, worldAnchor, portNormal, pkey, nodeGeometry, anchorOf, ascaleOf, frameBounds,
  localToWorld, DISC_R, FRAME_MARGIN,
} from './engine'
export { settle, settleStep, recomputeRegions, resolveOverlaps, REGION_PAD, SIB_GAP } from './relax'
export type { LegGeom, BoundaryExit, ExStub } from './wires'
export { computeLegs, legPaths, boundaryExits, existentialStubs } from './wires'
export type { Theme, Shape } from './paint'
export { paint, bubbleHues, highlightGroup, nextTheme, LIGHT, DARK, THEMES } from './paint'
export { drawShapes } from './canvas'
