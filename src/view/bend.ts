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

/** The rail radius shared by sealed atom, ref, and identity geometry. */
const RAIL_R = 2
const RAIL_ARC: NodeArc = { r: RAIL_R, a0: 0, a1: 2 * Math.PI }

/** Storage anchors are evenly spaced around the rim. The first angle retains
 * the established atom/ref geometry; identity paint deliberately omits the
 * order pip, so that phase is not a semantic first port for identities. */
function rimAnchors(prefix: 'a' | 'i', arity: number): Record<string, Vec2> {
  const anchors: Record<string, Vec2> = {}
  for (let index = 0; index < arity; index++) {
    const angle = Math.PI / 2 + index * 2 * Math.PI / Math.max(arity, 1)
    const point = polar(angle, RAIL_R)
    anchors[`${prefix}:${index}`] = {
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

function sealedGeometry(
  portAnchors: Readonly<Record<string, Vec2>>,
  headAnchor: Vec2 | null,
): NodeGeometry {
  return {
    outerRadius: RAIL_R + 0.5,
    arcs: [RAIL_ARC],
    headAnchor,
    portAnchors,
  }
}

/** A relation atom retains its argument rail and distinct relation-head port. */
export function atomGeometry(arity: number): NodeGeometry {
  return sealedGeometry(rimAnchors('a', arity), polar(headAngle(arity), RAIL_R))
}

/** A named relation ref retains its argument rail and has no relation-head port. */
export function refGeometry(arity: number): NodeGeometry {
  return sealedGeometry(rimAnchors('a', arity), null)
}

/**
 * A neutral equality bridge: one compact unlabelled rail with one evenly
 * spaced rim anchor for every identity storage port.
 */
export function identityGeometry(arity: number): NodeGeometry {
  return sealedGeometry(rimAnchors('i', arity), null)
}
