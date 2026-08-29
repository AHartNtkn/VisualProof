import type { PathSeg } from '../kernel/term/reduce'
import type { Term } from '../kernel/term/term'
import type { TrompGrid } from './tromp'
import { trompGrid } from './tromp'
import type { Vec2 } from './vec'
import { polar } from './vec'

/** Total angular width of the C-gap, centered on angle zero. */
export const GAP_ANGLE = Math.PI / 3
const LAMBDA_VIEW_PADDING_CELLS = 4

/** Match the corrected circular Painter's quarter-cell extension while
    retaining the four-cell view margin used around the structural grid. */
export function lambdaBarPadding(cols: number, scale = 1): number {
  return (2 * Math.PI - GAP_ANGLE) / (cols + LAMBDA_VIEW_PADDING_CELLS) * 0.25 * scale
}

export type NodeArc = {
  readonly r: number
  readonly a0: number
  readonly a1: number
  readonly kind: 'lam' | 'app' | 'rail'
  readonly hueRow: number
  readonly ownerPath: readonly PathSeg[]
}

export type NodeRadial = {
  readonly angle: number
  readonly r0: number
  readonly r1: number
  readonly kind: 'var' | 'output' | 'port'
  readonly hueRow: number | null
  readonly ownerPath: readonly PathSeg[]
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

/** Exact local geometry for one semantic node. */
export type NodeGeometry = {
  readonly outerRadius: number
  readonly arcs: readonly NodeArc[]
  readonly radials: readonly NodeRadial[]
  readonly headAnchor: Vec2 | null
  /** Port-anchor keys use kernel storage spelling (`out`, `f:0`, `a:0`, ...). */
  readonly portAnchors: Readonly<Record<string, Vec2>>
  readonly exitArc: { readonly r: number; readonly a0: number; readonly a1: number } | null
  readonly exitLine: readonly [Vec2, Vec2] | null
  readonly occurrences: readonly TermOccurrenceGeometry[]
}

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
  const theta = (col: number): number => (
    a0 + ((col + LAMBDA_VIEW_PADDING_CELLS / 2 + 0.5) / (cols + LAMBDA_VIEW_PADDING_CELLS)) * span
  )
  const radiusAtZero = rows + 2
  const radius = (row: number): number => radiusAtZero - row
  const rimR = radius(-railRows)
  return { a0, theta, radius, rimR, pierceR: rimR + 1 }
}

export function bendGrid(grid: TrompGrid): NodeGeometry {
  const { a0, theta, radius, pierceR } = bendMaps(grid.cols, grid.rows, grid.railRows)
  const arcs: NodeArc[] = grid.bars.map((bar, index) => {
    const pad = bar.kind === 'lam' ? lambdaBarPadding(grid.cols) : 0
    return {
      r: radius(bar.row),
      a0: theta(bar.colStart) - pad,
      a1: theta(bar.colEnd) + pad,
      kind: bar.kind,
      hueRow: bar.row,
      ownerPath: grid.barOwners[index] ?? [],
    }
  })
  const radials: NodeRadial[] = grid.stems.map((stem, index) => ({
    angle: theta(stem.col),
    r0: radius(stem.rowTop),
    r1: radius(stem.rowBottom),
    kind: stem.kind,
    hueRow: stem.kind === 'var' ? stem.rowTop : null,
    ownerPath: grid.stemOwners[index] ?? [],
  }))
  const portAnchors: Record<string, Vec2> = {}
  for (const rail of grid.rails) {
    const angle = theta(rail.stemCol)
    radials.push({
      angle, r0: radius(rail.row), r1: pierceR, kind: 'port', hueRow: null, ownerPath: [],
    })
    portAnchors[`f:${rail.slot}`] = polar(angle, pierceR)
  }

  const exitRadius = radius(grid.rows)
  const outputAngle = theta(grid.outputCol)
  const exitArc = { r: exitRadius, a0, a1: outputAngle }
  const outputAnchor = polar(0, pierceR)
  const exitLine: readonly [Vec2, Vec2] = [polar(a0, exitRadius), outputAnchor]
  portAnchors.out = outputAnchor

  const occurrences: TermOccurrenceGeometry[] = grid.occurrences.map((occurrence) => {
    const ownedByOccurrence = (owner: readonly PathSeg[] | null): boolean => (
      owner !== null && occurrence.path.every((segment, index) => owner[index] === segment)
    )
    const arcIndices = occurrence.path.length === 0
      ? arcs.map((_, index) => index)
      : grid.barOwners.flatMap((owner, index) => ownedByOccurrence(owner) ? [index] : [])
    const radialIndices = occurrence.path.length === 0
      ? radials.map((_, index) => index)
      : grid.stemOwners.flatMap((owner, index) => ownedByOccurrence(owner) ? [index] : [])
    const hit: TermOccurrenceHit = occurrence.hit.kind === 'exit'
      ? { kind: 'exit' }
      : occurrence.hit.kind === 'arcPoint'
        ? { kind: 'arcPoint', point: polar(theta(occurrence.hit.col), radius(occurrence.hit.row)) }
        : (() => {
            const radialHit = occurrence.hit
            const radialIndex = grid.stems.findIndex((stem) => (
              stem.kind === 'output'
              && stem.col === radialHit.col
              && stem.rowTop === radialHit.rowTop
              && stem.rowBottom === radialHit.rowBottom
            ))
            if (radialIndex < 0) {
              return { kind: 'arcPoint' as const, point: polar(theta(radialHit.col), radius(radialHit.rowBottom)) }
            }
            if (!radialIndices.includes(radialIndex)) radialIndices.push(radialIndex)
            return { kind: 'radial' as const, radialIndex }
          })()
    return {
      path: occurrence.path,
      depth: occurrence.depth,
      hit,
      arcIndices,
      radialIndices,
      includeExit: occurrence.path.length === 0,
    }
  })

  return {
    outerRadius: pierceR + 0.5,
    arcs,
    radials,
    headAnchor: null,
    portAnchors,
    exitArc,
    exitLine,
    occurrences,
  }
}

export function termGeometry(term: Term, interfaceArity?: number): NodeGeometry {
  return bendGrid(trompGrid(term, interfaceArity))
}

const RAIL_R = 2
const RAIL_ARC: NodeArc = {
  r: RAIL_R, a0: 0, a1: 2 * Math.PI, kind: 'rail', hueRow: 0, ownerPath: [],
}

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

function headAngle(arity: number): number {
  return arity === 0 ? Math.PI / 2 : Math.PI / 2 - Math.PI / arity
}

function circularGeometry(keys: readonly string[]): NodeGeometry {
  return {
    outerRadius: RAIL_R + 0.5,
    arcs: [RAIL_ARC],
    radials: [],
    headAnchor: null,
    portAnchors: rimAnchors(keys),
    exitArc: null,
    exitLine: null,
    occurrences: [],
  }
}

export function atomGeometry(arity: number): NodeGeometry {
  const geometry = circularGeometry(Array.from({ length: arity }, (_, index) => `a:${index}`))
  return { ...geometry, headAnchor: polar(headAngle(arity), RAIL_R) }
}

export function refGeometry(arity: number): NodeGeometry {
  return circularGeometry(Array.from({ length: arity }, (_, index) => `a:${index}`))
}

export function identityGeometry(arity: number): NodeGeometry {
  const portAnchors: Record<string, Vec2> = {}
  for (let index = 0; index < arity; index++) portAnchors[`i:${index}`] = { x: 0, y: 0 }
  return {
    outerRadius: 0,
    arcs: [],
    radials: [],
    headAnchor: null,
    portAnchors,
    exitArc: null,
    exitLine: null,
    occurrences: [],
  }
}
