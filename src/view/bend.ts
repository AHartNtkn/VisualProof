import type { Vec2 } from './vec'
import { polar } from './vec'
import type { TrompGrid } from './tromp'
import type { PathSeg } from '../kernel/term/reduce'

/** Total angular width of the C-gap, centered on angle 0 (the output exit). */
export const GAP_ANGLE = Math.PI / 3

export type NodeArc = {
  readonly r: number
  readonly a0: number
  readonly a1: number
  readonly kind: 'lam' | 'app' | 'rail'
  /** Hue identity: the grid row of the bar (lam bars: binder identity). */
  readonly hueRow: number
}

export type NodeRadial = {
  readonly angle: number
  readonly r0: number
  readonly r1: number
  readonly kind: 'var' | 'output' | 'port'
  /** For var stems: the binder bar row they hang from; otherwise null. */
  readonly hueRow: number | null
}

export type NodeGeometry = {
  /** Radius enclosing everything including pierce stubs and the exit. */
  readonly outerRadius: number
  readonly arcs: readonly NodeArc[]
  readonly radials: readonly NodeRadial[]
  readonly outputAnchor: Vec2
  /** The head-port rim anchor of an atom (the wire designating its relation);
      null for every node without a head port (terms, refs, bodies). */
  readonly headAnchor: Vec2 | null
  readonly portAnchors: Readonly<Record<string, Vec2>>
  /** Innermost arc carrying the output around to the gap edge (null when the
      output column already sits at the first column next to the gap). */
  readonly exitArc: { readonly r: number; readonly a0: number; readonly a1: number } | null
  /** The output's straight run out of the anatomy — term nodes only. Refs and
      atoms have no term output, so they emit no exit line (law 4: non-term
      nodes must not fabricate a second leg). */
  readonly exitLine: readonly [Vec2, Vec2] | null
  readonly occurrences: readonly TermOccurrenceGeometry[]
}

export type TermOccurrenceHit =
  | { readonly kind: 'radial'; readonly radialIndex: number }
  | { readonly kind: 'arcPoint'; readonly point: Vec2 }
  | { readonly kind: 'exit' }

export type TermOccurrenceGeometry = {
  readonly path: readonly PathSeg[]
  readonly depth: number
  readonly hit: TermOccurrenceHit
  readonly arcIndices: readonly number[]
  readonly radialIndices: readonly number[]
  readonly includeExit: boolean
}

/**
 * Bend a rectilinear Tromp grid into an incomplete circle (spec option A):
 * columns map to angles inside [gap/2, 2π − gap/2]; rows map to radii
 * decreasing inward, with port rails (negative rows) landing OUTSIDE the rim
 * as radial pierces; the output runs to the innermost ring, arcs to the gap
 * edge, and exits straight through the gap to an anchor at angle 0.
 */
/** The col→angle and row→radius maps of the bend, parameterized by the frame
    (cols, rows, railRows). Real-valued arguments are legal — the morph layer
    interpolates frames and coordinates through these same formulas. */
export type BendMaps = {
  readonly a0: number
  readonly theta: (col: number) => number
  readonly radius: (row: number) => number
  readonly rimR: number
  readonly pierceR: number
}

export function bendMaps(cols: number, rows: number, railRows: number): BendMaps {
  const a0 = GAP_ANGLE / 2
  const span = 2 * Math.PI - GAP_ANGLE
  const theta = (col: number): number => a0 + ((col + 0.5) / cols) * span
  // row 0 sits at radius rowsBelow + 2 so the innermost row keeps radius 2
  const r0 = rows + 2
  const radius = (row: number): number => r0 - row
  const rimR = radius(-railRows) // outermost rail ring
  return { a0, theta, radius, rimR, pierceR: rimR + 1 }
}

export function bendGrid(g: TrompGrid): NodeGeometry {
  const { a0, theta, radius, pierceR } = bendMaps(g.cols, g.rows, g.railRows)

  const arcs: NodeArc[] = g.bars.map((b) => ({
    r: radius(b.row),
    a0: theta(b.colStart),
    a1: theta(b.colEnd),
    kind: b.kind,
    hueRow: b.row,
  }))
  const radials: NodeRadial[] = g.stems.map((s) => ({
    angle: theta(s.col),
    r0: radius(s.rowTop),
    r1: radius(s.rowBottom),
    kind: s.kind,
    hueRow: s.kind === 'var' ? s.rowTop : null,
  }))
  // one outward pierce per rail, its tip being the port anchor
  const portAnchors: Record<string, Vec2> = {}
  for (const rail of g.rails) {
    const angle = theta(rail.stemCol)
    radials.push({ angle, r0: radius(rail.row), r1: pierceR, kind: 'port', hueRow: null })
    portAnchors[rail.name] = polar(angle, pierceR)
  }
  // output exit: innermost ring arc to the gap edge, then straight out.
  // theta() centers columns, so outAngle always clears the gap edge here —
  // the null exitArc case belongs to atomGeometry, which has no ring to arc.
  const exitR = radius(g.rows)
  const outAngle = theta(g.outputCol)
  const exitArc = { r: exitR, a0, a1: outAngle }
  const outputAnchor = polar(0, pierceR)
  const exitLine: readonly [Vec2, Vec2] = [polar(a0, exitR), outputAnchor]
  const occurrences: TermOccurrenceGeometry[] = g.occurrences.map((occurrence) => {
    const ownedByOccurrence = (owner: readonly PathSeg[] | null): boolean => owner !== null
      && occurrence.path.every((segment, index) => owner[index] === segment)
    const arcIndices = occurrence.path.length === 0
      ? arcs.map((_, index) => index)
      : g.barOwners.flatMap((owner, index) => ownedByOccurrence(owner) ? [index] : [])
    const radialIndices = occurrence.path.length === 0
      ? radials.map((_, index) => index)
      : g.stemOwners.flatMap((owner, index) => ownedByOccurrence(owner) ? [index] : [])
    const hit: TermOccurrenceHit = occurrence.hit.kind === 'exit'
      ? { kind: 'exit' }
      : occurrence.hit.kind === 'arcPoint'
        ? { kind: 'arcPoint', point: polar(theta(occurrence.hit.col), radius(occurrence.hit.row)) }
        : (() => {
          const radialHit = occurrence.hit
          if (radialHit.kind !== 'radial') throw new Error('unreachable occurrence hit')
          const radialIndex = g.stems.findIndex((stem) => stem.kind === 'output'
            && stem.col === radialHit.col
            && stem.rowTop === radialHit.rowTop
            && stem.rowBottom === radialHit.rowBottom)
          if (radialIndex < 0) {
            return { kind: 'arcPoint' as const, point: polar(theta(radialHit.col), radius(radialHit.rowBottom)) }
          }
          if (!radialIndices.includes(radialIndex)) radialIndices.push(radialIndex)
          return { kind: 'radial' as const, radialIndex }
        })()
    return { path: occurrence.path, depth: occurrence.depth, hit, arcIndices, radialIndices,
      includeExit: occurrence.path.length === 0 }
  })

  return {
    outerRadius: pierceR + 0.5,
    arcs,
    radials,
    outputAnchor,
    headAnchor: null,
    portAnchors,
    exitArc,
    exitLine,
    occurrences,
  }
}

/** The rail radius of every sealed disc (atom / ref / body). */
const RAIL_R = 2

/** The n numbered ports of a sealed disc, evenly spaced clockwise (canvas
    y-down) from a0/p0 at the top (angle π/2 — where the port-order pip sits). */
function ringAngles(n: number): number[] {
  const out: number[] = []
  for (let i = 0; i < n; i++) out.push(Math.PI / 2 + (i * 2 * Math.PI) / Math.max(n, 1))
  return out
}

/** The rim angle of a sealed disc's ONE non-numbered port — an atom's head or a
    body's output. It bisects the arc between the last and first numbered port
    (the widest empty slot), so it never coincides with an argument at any arity.
    A port-less disc (arity 0) puts it at the top. */
function mainAngle(n: number): number {
  return n === 0 ? Math.PI / 2 : Math.PI / 2 - Math.PI / n
}

/** Anchor keys use portKey spelling without the colon ('a0', 'p0', …) purely as
    local labels; anchorOf maps arg/freeVar ports onto them. */
function railAnchors(prefix: string, n: number): Record<string, Vec2> {
  const angles = ringAngles(n)
  const out: Record<string, Vec2> = {}
  for (let i = 0; i < n; i++) out[`${prefix}${i}`] = polar(angles[i]!, RAIL_R)
  return out
}

const RAIL_ARC: NodeArc = { r: RAIL_R, a0: 0, a1: 2 * Math.PI, kind: 'rail', hueRow: 0 }

/**
 * An atom (a relation application) has no term structure: a bare rail circle
 * with `arity` argument ports on the rim plus one HEAD port designating its
 * relation wire. A wire meets the drawn circle directly; the port-order pip
 * marks a0's direction and ports read clockwise from it.
 */
export function atomGeometry(arity: number): NodeGeometry {
  return {
    outerRadius: RAIL_R + 0.5,
    arcs: [RAIL_ARC],
    radials: [],
    outputAnchor: polar(0, RAIL_R),
    headAnchor: polar(mainAngle(arity), RAIL_R),
    portAnchors: railAnchors('a', arity),
    exitArc: null,
    exitLine: null,
    occurrences: [],
  }
}

/**
 * A relation ref is a named sealed disc with `arity` argument ports and no head
 * (the name designates the relation, so no head wire). The paint layer draws
 * the name as the disc's label from the node's defId (law 2: named nodes, not
 * text on anatomy).
 */
export function refGeometry(arity: number): NodeGeometry {
  return {
    outerRadius: RAIL_R + 0.5,
    arcs: [RAIL_ARC],
    radials: [],
    outputAnchor: polar(0, RAIL_R),
    headAnchor: null,
    portAnchors: railAnchors('a', arity),
    exitArc: null,
    exitLine: null,
    occurrences: [],
  }
}

/**
 * A comprehension body renders as a single SEALED disc — its internal diagram
 * is never inlined (authored/inspected in the relation workspace). It carries
 * an OUTPUT port (the relation it defines) plus `paramCount` parameter ports
 * p0…p(k-1) attaching to outer wires. Output takes the head slot; params spread
 * like an atom's arguments.
 */
export function bodyGeometry(paramCount: number): NodeGeometry {
  return {
    outerRadius: RAIL_R + 0.5,
    arcs: [RAIL_ARC],
    radials: [],
    outputAnchor: polar(mainAngle(paramCount), RAIL_R),
    headAnchor: null,
    portAnchors: railAnchors('p', paramCount),
    exitArc: null,
    exitLine: null,
    occurrences: [],
  }
}
