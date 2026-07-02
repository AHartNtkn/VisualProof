import type { Vec2 } from './vec'
import { polar } from './vec'
import type { TrompGrid } from './tromp'

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
  readonly glyphs: readonly { readonly pos: Vec2; readonly constId: string }[]
  readonly outputAnchor: Vec2
  readonly portAnchors: Readonly<Record<string, Vec2>>
  /** Innermost arc carrying the output around to the gap edge (null when the
      output column already sits at the first column next to the gap). */
  readonly exitArc: { readonly r: number; readonly a0: number; readonly a1: number } | null
  /** The output's straight run out of the anatomy — term nodes only. Refs and
      atoms have no term output, so they emit no exit line (law 4: non-term
      nodes must not fabricate a second leg). */
  readonly exitLine: readonly [Vec2, Vec2] | null
}

/**
 * Bend a rectilinear Tromp grid into an incomplete circle (spec option A):
 * columns map to angles inside [gap/2, 2π − gap/2]; rows map to radii
 * decreasing inward, with port rails (negative rows) landing OUTSIDE the rim
 * as radial pierces; the output runs to the innermost ring, arcs to the gap
 * edge, and exits straight through the gap to an anchor at angle 0.
 */
export function bendGrid(g: TrompGrid): NodeGeometry {
  const a0 = GAP_ANGLE / 2
  const span = 2 * Math.PI - GAP_ANGLE
  const theta = (col: number): number => a0 + ((col + 0.5) / g.cols) * span
  // row 0 sits at radius rowsBelow + 2 so the innermost row keeps radius 2
  const r0 = g.rows + 2
  const radius = (row: number): number => r0 - row
  const rimR = radius(-g.railRows) // outermost rail ring
  const pierceR = rimR + 1

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

  const glyphs = g.glyphs.map((gl) => ({ pos: polar(theta(gl.col), radius(gl.row)), constId: gl.constId }))

  return {
    outerRadius: pierceR + 0.5,
    arcs,
    radials,
    glyphs,
    outputAnchor,
    portAnchors,
    exitArc,
    exitLine,
  }
}

/**
 * Atoms (relation-variable applications) and relation refs have no term
 * structure: a small disc with arg anchors spread evenly around it. Anchor
 * keys use portKey spelling without the colon ('a0', 'a1', …) purely as local
 * labels. A ref's name is not a geometry glyph — the paint layer draws it as
 * the disc's label from the node's defId (law 2: named nodes, not text on
 * anatomy).
 */
export function atomGeometry(arity: number): NodeGeometry {
  const r = 2
  const pierce = r + 1
  const portAnchors: Record<string, Vec2> = {}
  const radials: NodeRadial[] = []
  for (let i = 0; i < arity; i++) {
    const angle = Math.PI / 2 + (i * 2 * Math.PI) / Math.max(arity, 1)
    portAnchors[`a${i}`] = polar(angle, pierce)
    radials.push({ angle, r0: r, r1: pierce, kind: 'port', hueRow: null })
  }
  return {
    outerRadius: pierce + 0.5,
    arcs: [{ r, a0: 0, a1: 2 * Math.PI, kind: 'rail', hueRow: 0 }],
    radials,
    glyphs: [],
    outputAnchor: polar(0, pierce),
    portAnchors,
    exitArc: null,
    exitLine: null,
  }
}
