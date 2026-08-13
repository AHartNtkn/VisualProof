import type { Vec2 } from './vec'
import { polar } from './vec'

export type NodeArc = {
  readonly r: number
  readonly a0: number
  readonly a1: number
}

/**
 * Exact local geometry for one semantic node.
 *
 * Port-anchor keys use the kernel's storage spelling (`a:0`, `i:0`, ...).
 * Identity indices are locators only: neither this record nor paint assigns
 * them a semantic label or reading order.
 */
export type NodeGeometry = {
  readonly outerRadius: number
  readonly arcs: readonly NodeArc[]
  readonly headAnchor: Vec2 | null
  readonly portAnchors: Readonly<Record<string, Vec2>>
}

/** The rail radius shared by sealed atom and ref geometry. */
const RAIL_R = 2
const RAIL_ARC: NodeArc = { r: RAIL_R, a0: 0, a1: 2 * Math.PI }

/** Storage/view anchors are evenly spaced around the rim. */
function rimAnchors(keys: readonly string[]): Record<string, Vec2> {
  const anchors: Record<string, Vec2> = {}
  for (let index = 0; index < keys.length; index++) {
    const angle = Math.PI / 2 + index * 2 * Math.PI / Math.max(keys.length, 1)
    const point = polar(angle, RAIL_R)
    anchors[keys[index]!] = {
      x: Math.abs(point.x) < 1e-12 ? 0 : point.x,
      y: Math.abs(point.y) < 1e-12 ? 0 : point.y,
    }
  }
  return anchors
}

/** The atom head bisects the widest argument-anchor gap. */
function headAngle(arity: number): number {
  return arity === 0 ? Math.PI / 2 : Math.PI / 2 - Math.PI / arity
}

function circularGeometry(keys: readonly string[]): NodeGeometry {
  return {
    outerRadius: RAIL_R + 0.5,
    arcs: [RAIL_ARC],
    headAnchor: null,
    portAnchors: rimAnchors(keys),
  }
}

/** A relation atom retains its argument rail and distinct relation-head port. */
export function atomGeometry(arity: number): NodeGeometry {
  const geometry = circularGeometry(Array.from({ length: arity }, (_, index) => `a:${index}`))
  return { ...geometry, headAnchor: polar(headAngle(arity), RAIL_R) }
}

/** A named relation ref retains its argument rail and has no relation-head port. */
export function refGeometry(arity: number): NodeGeometry {
  return circularGeometry(Array.from({ length: arity }, (_, index) => `a:${index}`))
}

/** Equality uses the same circular geometry as a dangling existential. */
export function identityGeometry(arity: number): NodeGeometry {
  return circularGeometry(Array.from({ length: arity }, (_, index) => `i:${index}`))
}

