import type { Term } from '../kernel/term/term'
import { freePorts } from '../kernel/term/term'

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

export type Glyph = { readonly col: number; readonly row: number; readonly constId: string }

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
  readonly stems: readonly Stem[]
  readonly glyphs: readonly Glyph[]
  readonly outputCol: number
  readonly rails: readonly Rail[]
}

type Box = {
  readonly width: number
  readonly bottom: number
  readonly stemCol: number
  readonly bars: readonly Bar[]
  readonly stems: readonly Stem[]
  readonly glyphs: readonly Glyph[]
  readonly ports: ReadonlyMap<string, readonly number[]>
}

function shifted(b: Box, dc: number): Box {
  if (dc === 0) return b
  return {
    width: b.width,
    bottom: b.bottom,
    stemCol: b.stemCol + dc,
    bars: b.bars.map((x) => ({ ...x, colStart: x.colStart + dc, colEnd: x.colEnd + dc })),
    stems: b.stems.map((x) => ({ ...x, col: x.col + dc })),
    glyphs: b.glyphs.map((x) => ({ ...x, col: x.col + dc })),
    ports: new Map([...b.ports].map(([n, cols]) => [n, cols.map((c) => c + dc)])),
  }
}

function mergePorts(a: ReadonlyMap<string, readonly number[]>, b: ReadonlyMap<string, readonly number[]>): Map<string, readonly number[]> {
  const out = new Map<string, readonly number[]>(a)
  for (const [n, cols] of b) out.set(n, [...(out.get(n) ?? []), ...cols])
  return out
}

function layoutAt(t: Term, depth: number): Box {
  switch (t.kind) {
    case 'bvar': {
      // assertWellFormedTerm guarantees index < depth for diagram node terms
      const barRow = depth - 1 - t.index
      return {
        width: 1, bottom: depth, stemCol: 0, bars: [], glyphs: [], ports: new Map(),
        stems: [{ col: 0, rowTop: barRow, rowBottom: depth, kind: 'var' }],
      }
    }
    case 'port':
      return {
        width: 1, bottom: depth, stemCol: 0, bars: [], glyphs: [],
        ports: new Map([[t.name, [0]]]),
        // runs from row 0 down through the binder block; the rail drop above
        // row 0 is added at assembly once the rail row is known
        stems: depth > 0 ? [{ col: 0, rowTop: 0, rowBottom: depth, kind: 'port', portName: t.name }] : [],
      }
    case 'const':
      return {
        width: 1, bottom: depth, stemCol: 0, bars: [], ports: new Map(),
        glyphs: [{ col: 0, row: depth, constId: t.id }],
        stems: [],
      }
    case 'lam': {
      const inner = layoutAt(t.body, depth + 1)
      return {
        ...inner,
        bars: [...inner.bars, { row: depth, colStart: 0, colEnd: inner.width - 1, kind: 'lam' }],
      }
    }
    case 'app': {
      const f = layoutAt(t.fn, depth)
      const a = shifted(layoutAt(t.arg, depth), f.width)
      const barRow = Math.max(f.bottom, a.bottom) + 1
      return {
        width: f.width + a.width,
        bottom: barRow,
        stemCol: f.stemCol,
        bars: [...f.bars, ...a.bars, { row: barRow, colStart: f.stemCol, colEnd: a.stemCol, kind: 'app' }],
        stems: [
          ...f.stems, ...a.stems,
          { col: f.stemCol, rowTop: f.bottom, rowBottom: barRow, kind: 'output' },
          { col: a.stemCol, rowTop: a.bottom, rowBottom: barRow, kind: 'output' },
        ],
        glyphs: [...f.glyphs, ...a.glyphs],
        ports: mergePorts(f.ports, a.ports),
      }
    }
  }
}

export function trompGrid(t: Term): TrompGrid {
  const box = layoutAt(t, 0)
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
    stems: [...box.stems, ...drops, output],
    glyphs: box.glyphs,
    outputCol: box.stemCol,
    rails,
  }
}
