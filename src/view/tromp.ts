import type { Term } from '../kernel/term/term'
import { freePorts } from '../kernel/term/term'
import type { PathSeg } from '../kernel/term/reduce'

export type Bar = {
  readonly row: number
  readonly colStart: number
  readonly colEnd: number
  readonly kind: 'lam' | 'app' | 'rail'
}

export type Stem = {
  readonly col: number
  readonly rowTop: number
  readonly rowBottom: number
  readonly kind: 'var' | 'output' | 'port'
  readonly portName?: string
}

export type Rail = {
  readonly name: string
  readonly row: number
  readonly colStart: number
  readonly colEnd: number
  readonly stemCol: number
}

/**
 * Classic rectilinear Tromp layout on an integer grid. Binder bars sit at
 * row = binder depth (outermost = 0); variables hang from their binder's bar;
 * an application joins its two output stems one row below the deeper side;
 * free ports get rails stacked ABOVE row 0 (negative rows) in first-occurrence
 * order, one per distinct name — exactly mirroring requiredPorts.
 */
export type TrompGrid = {
  readonly cols: number
  /** Rows 0..rows: binder block + application structure + final output row. */
  readonly rows: number
  /** Port rails occupy rows -1..-railRows. */
  readonly railRows: number
  readonly bars: readonly Bar[]
  /** Exact syntax occurrence that introduced each painted bar; null for shared port rails. */
  readonly barOwners: readonly (readonly PathSeg[] | null)[]
  readonly stems: readonly Stem[]
  /** Exact syntax occurrence that introduced each painted stem; null for shared port drops. */
  readonly stemOwners: readonly (readonly PathSeg[] | null)[]
  readonly outputCol: number
  readonly rails: readonly Rail[]
  readonly occurrences: readonly GridOccurrence[]
}

export type GridOccurrence = {
  readonly path: readonly PathSeg[]
  readonly depth: number
  readonly layoutDepth: number
  readonly colStart: number
  readonly colEnd: number
  readonly bottom: number
  readonly hit: GridOccurrenceHit
}

export type GridOccurrenceHit =
  | { readonly kind: 'radial'; readonly col: number; readonly rowTop: number; readonly rowBottom: number }
  | { readonly kind: 'arcPoint'; readonly row: number; readonly col: number }
  | { readonly kind: 'exit' }

type Box = {
  readonly width: number
  readonly bottom: number
  readonly stemCol: number
  readonly bars: readonly Bar[]
  readonly barOwners: readonly (readonly PathSeg[])[]
  readonly stems: readonly Stem[]
  readonly stemOwners: readonly (readonly PathSeg[])[]
  readonly ports: ReadonlyMap<string, readonly number[]>
  readonly occurrences: readonly GridOccurrence[]
}

function shifted(b: Box, dc: number): Box {
  if (dc === 0) return b
  return {
    width: b.width,
    bottom: b.bottom,
    stemCol: b.stemCol + dc,
    bars: b.bars.map((x) => ({ ...x, colStart: x.colStart + dc, colEnd: x.colEnd + dc })),
    barOwners: b.barOwners,
    stems: b.stems.map((x) => ({ ...x, col: x.col + dc })),
    stemOwners: b.stemOwners,
    ports: new Map([...b.ports].map(([n, cols]) => [n, cols.map((c) => c + dc)])),
    occurrences: b.occurrences.map((occurrence) => ({
      ...occurrence,
      colStart: occurrence.colStart + dc,
      colEnd: occurrence.colEnd + dc,
      hit: occurrence.hit.kind === 'exit' ? occurrence.hit
        : occurrence.hit.kind === 'arcPoint' ? { ...occurrence.hit, col: occurrence.hit.col + dc }
          : { ...occurrence.hit, col: occurrence.hit.col + dc },
    })),
  }
}

function mergePorts(a: ReadonlyMap<string, readonly number[]>, b: ReadonlyMap<string, readonly number[]>): Map<string, readonly number[]> {
  const out = new Map<string, readonly number[]>(a)
  for (const [n, cols] of b) out.set(n, [...(out.get(n) ?? []), ...cols])
  return out
}

function layoutAt(t: Term, depth: number, path: readonly PathSeg[]): Box {
  switch (t.kind) {
    case 'bvar': {
      // assertWellFormedTerm guarantees index < depth for diagram node terms
      const barRow = depth - 1 - t.index
      return {
        width: 1, bottom: depth, stemCol: 0, bars: [], barOwners: [], ports: new Map(),
        stems: [{ col: 0, rowTop: barRow, rowBottom: depth, kind: 'var' }],
        stemOwners: [path],
        occurrences: [{ path, depth: path.length, layoutDepth: depth, colStart: 0, colEnd: 0, bottom: depth,
          hit: { kind: 'radial', col: 0, rowTop: barRow, rowBottom: depth } }],
      }
    }
    case 'port':
      return {
        width: 1, bottom: depth, stemCol: 0, bars: [], barOwners: [],
        ports: new Map([[t.name, [0]]]),
        // runs from row 0 down through the binder block; the rail drop above
        // row 0 is added at assembly once the rail row is known
        stems: depth > 0 ? [{ col: 0, rowTop: 0, rowBottom: depth, kind: 'port', portName: t.name }] : [],
        stemOwners: depth > 0 ? [path] : [],
        occurrences: [{ path, depth: path.length, layoutDepth: depth, colStart: 0, colEnd: 0, bottom: depth,
          hit: { kind: 'radial', col: 0, rowTop: 0, rowBottom: depth } }],
      }
    case 'lam': {
      const inner = layoutAt(t.body, depth + 1, [...path, 'body'])
      const bodyPath = [...path, 'body']
      return {
        ...inner,
        bars: [...inner.bars, { row: depth, colStart: 0, colEnd: inner.width - 1, kind: 'lam' }],
        barOwners: [...inner.barOwners, path],
        occurrences: [
          { path, depth: path.length, layoutDepth: depth, colStart: 0, colEnd: inner.width - 1,
            bottom: inner.bottom, hit: { kind: 'arcPoint', row: depth, col: inner.stemCol } },
          ...inner.occurrences.map((occurrence) => occurrence.path.length === bodyPath.length
            && occurrence.path.every((segment, index) => segment === bodyPath[index])
            ? { ...occurrence, hit: { kind: 'arcPoint' as const, row: depth, col: inner.stemCol } }
            : occurrence),
        ],
      }
    }
    case 'app': {
      const f = layoutAt(t.fn, depth, [...path, 'fn'])
      const a = shifted(layoutAt(t.arg, depth, [...path, 'arg']), f.width)
      const barRow = Math.max(f.bottom, a.bottom) + 1
      const childHit = (occurrences: readonly GridOccurrence[], child: Box): GridOccurrence[] =>
        occurrences.map((occurrence, index) => index === 0 ? {
          ...occurrence,
          hit: { kind: 'radial' as const, col: child.stemCol, rowTop: child.bottom, rowBottom: barRow },
        } : occurrence)
      return {
        width: f.width + a.width,
        bottom: barRow,
        stemCol: f.stemCol,
        bars: [...f.bars, ...a.bars, { row: barRow, colStart: f.stemCol, colEnd: a.stemCol, kind: 'app' }],
        barOwners: [...f.barOwners, ...a.barOwners, path],
        stems: [
          ...f.stems, ...a.stems,
          { col: f.stemCol, rowTop: f.bottom, rowBottom: barRow, kind: 'output' },
          { col: a.stemCol, rowTop: a.bottom, rowBottom: barRow, kind: 'output' },
        ],
        stemOwners: [
          ...f.stemOwners, ...a.stemOwners,
          f.occurrences[0]!.path,
          a.occurrences[0]!.path,
        ],
        ports: mergePorts(f.ports, a.ports),
        occurrences: [
          { path, depth: path.length, layoutDepth: depth, colStart: 0, colEnd: f.width + a.width - 1,
            bottom: barRow, hit: { kind: 'radial', col: f.stemCol, rowTop: f.bottom, rowBottom: barRow } },
          ...childHit(f.occurrences, f), ...childHit(a.occurrences, a),
        ],
      }
    }
  }
}

export function trompGrid(t: Term): TrompGrid {
  const box = layoutAt(t, 0, [])
  const names = freePorts(t)
  const rails: Rail[] = names.map((name, i) => {
    const cols = box.ports.get(name)
    if (cols === undefined || cols.length === 0) {
      throw new Error(`port '${name}' has no occurrence columns; layout is inconsistent with freePorts`)
    }
    return {
      name,
      row: -(i + 1),
      colStart: Math.min(...cols),
      colEnd: Math.max(...cols),
      stemCol: Math.min(...cols),
    }
  })
  const drops: Stem[] = rails.flatMap((rail) =>
    (box.ports.get(rail.name) ?? []).map((col): Stem => ({
      col, rowTop: rail.row, rowBottom: 0, kind: 'port', portName: rail.name,
    })))
  const output: Stem = { col: box.stemCol, rowTop: box.bottom, rowBottom: box.bottom + 1, kind: 'output' }
  return {
    cols: box.width,
    rows: box.bottom + 1,
    railRows: rails.length,
    bars: [...box.bars, ...rails.map((r): Bar => ({ row: r.row, colStart: r.colStart, colEnd: r.colEnd, kind: 'rail' }))],
    barOwners: [...box.barOwners, ...rails.map(() => null)],
    stems: [...box.stems, ...drops, output],
    stemOwners: [...box.stemOwners, ...drops.map(() => null), []],
    outputCol: box.stemCol,
    rails,
    occurrences: box.occurrences.map((occurrence, index) => index === 0
      ? { ...occurrence, hit: { kind: 'exit' as const } }
      : occurrence),
  }
}
