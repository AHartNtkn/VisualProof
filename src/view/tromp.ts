import type { PathSeg } from '../kernel/term/reduce'
import type { Term } from '../kernel/term/term'
import { assertWellFormedTerm, freeArity } from '../kernel/term/term'

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
  readonly portSlot?: number
}

export type Rail = {
  readonly slot: number
  readonly row: number
  readonly colStart: number
  readonly colEnd: number
  readonly stemCol: number
}

export type GridOccurrenceHit =
  | { readonly kind: 'radial'; readonly col: number; readonly rowTop: number; readonly rowBottom: number }
  | { readonly kind: 'arcPoint'; readonly row: number; readonly col: number }
  | { readonly kind: 'exit' }

export type GridOccurrence = {
  readonly path: readonly PathSeg[]
  readonly depth: number
  readonly layoutDepth: number
  readonly colStart: number
  readonly colEnd: number
  readonly bottom: number
  readonly hit: GridOccurrenceHit
}

export type TrompGrid = {
  readonly cols: number
  readonly rows: number
  readonly railRows: number
  readonly bars: readonly Bar[]
  readonly barOwners: readonly (readonly PathSeg[] | null)[]
  readonly stems: readonly Stem[]
  readonly stemOwners: readonly (readonly PathSeg[] | null)[]
  readonly outputCol: number
  readonly rails: readonly Rail[]
  readonly occurrences: readonly GridOccurrence[]
}

type Box = {
  readonly width: number
  readonly bottom: number
  readonly stemCol: number
  readonly bars: readonly Bar[]
  readonly barOwners: readonly (readonly PathSeg[])[]
  readonly stems: readonly Stem[]
  readonly stemOwners: readonly (readonly PathSeg[])[]
  readonly free: ReadonlyMap<number, readonly number[]>
  readonly occurrences: readonly GridOccurrence[]
}

function shifted(box: Box, colDelta: number): Box {
  if (colDelta === 0) return box
  return {
    width: box.width,
    bottom: box.bottom,
    stemCol: box.stemCol + colDelta,
    bars: box.bars.map((bar) => ({
      ...bar,
      colStart: bar.colStart + colDelta,
      colEnd: bar.colEnd + colDelta,
    })),
    barOwners: box.barOwners,
    stems: box.stems.map((stem) => ({ ...stem, col: stem.col + colDelta })),
    stemOwners: box.stemOwners,
    free: new Map([...box.free].map(([slot, cols]) => [slot, cols.map((col) => col + colDelta)])),
    occurrences: box.occurrences.map((occurrence) => ({
      ...occurrence,
      colStart: occurrence.colStart + colDelta,
      colEnd: occurrence.colEnd + colDelta,
      hit: occurrence.hit.kind === 'exit'
        ? occurrence.hit
        : { ...occurrence.hit, col: occurrence.hit.col + colDelta },
    })),
  }
}

function mergeFree(
  left: ReadonlyMap<number, readonly number[]>,
  right: ReadonlyMap<number, readonly number[]>,
): Map<number, readonly number[]> {
  const merged = new Map<number, readonly number[]>(left)
  for (const [slot, cols] of right) {
    merged.set(slot, [...(merged.get(slot) ?? []), ...cols])
  }
  return merged
}

function layoutAt(term: Term, binderDepth: number, path: readonly PathSeg[]): Box {
  switch (term.kind) {
    case 'bound': {
      const binderRow = binderDepth - 1 - term.index
      return {
        width: 1,
        bottom: binderDepth,
        stemCol: 0,
        bars: [],
        barOwners: [],
        stems: [{ col: 0, rowTop: binderRow, rowBottom: binderDepth, kind: 'var' }],
        stemOwners: [path],
        free: new Map(),
        occurrences: [{
          path,
          depth: path.length,
          layoutDepth: binderDepth,
          colStart: 0,
          colEnd: 0,
          bottom: binderDepth,
          hit: { kind: 'radial', col: 0, rowTop: binderRow, rowBottom: binderDepth },
        }],
      }
    }
    case 'free':
      return {
        width: 1,
        bottom: binderDepth,
        stemCol: 0,
        bars: [],
        barOwners: [],
        stems: binderDepth > 0
          ? [{ col: 0, rowTop: 0, rowBottom: binderDepth, kind: 'port', portSlot: term.slot }]
          : [],
        stemOwners: binderDepth > 0 ? [path] : [],
        free: new Map([[term.slot, [0]]]),
        occurrences: [{
          path,
          depth: path.length,
          layoutDepth: binderDepth,
          colStart: 0,
          colEnd: 0,
          bottom: binderDepth,
          hit: { kind: 'radial', col: 0, rowTop: 0, rowBottom: binderDepth },
        }],
      }
    case 'lambda': {
      const bodyPath = [...path, 'body'] as const
      const body = layoutAt(term.body, binderDepth + 1, bodyPath)
      return {
        ...body,
        bars: [
          ...body.bars,
          { row: binderDepth, colStart: 0, colEnd: body.width - 1, kind: 'lam' },
        ],
        barOwners: [...body.barOwners, path],
        occurrences: [
          {
            path,
            depth: path.length,
            layoutDepth: binderDepth,
            colStart: 0,
            colEnd: body.width - 1,
            bottom: body.bottom,
            hit: { kind: 'arcPoint', row: binderDepth, col: body.stemCol },
          },
          ...body.occurrences.map((occurrence) => (
            occurrence.path.length === bodyPath.length
            && occurrence.path.every((segment, index) => segment === bodyPath[index])
              ? { ...occurrence, hit: { kind: 'arcPoint' as const, row: binderDepth, col: body.stemCol } }
              : occurrence
          )),
        ],
      }
    }
    case 'application': {
      const fn = layoutAt(term.fn, binderDepth, [...path, 'fn'])
      const argument = shifted(layoutAt(term.argument, binderDepth, [...path, 'argument']), fn.width)
      const barRow = Math.max(fn.bottom, argument.bottom) + 1
      const childHits = (occurrences: readonly GridOccurrence[], child: Box): GridOccurrence[] => (
        occurrences.map((occurrence, index) => index === 0
          ? {
              ...occurrence,
              hit: { kind: 'radial' as const, col: child.stemCol, rowTop: child.bottom, rowBottom: barRow },
            }
          : occurrence)
      )
      return {
        width: fn.width + argument.width,
        bottom: barRow,
        stemCol: fn.stemCol,
        bars: [
          ...fn.bars,
          ...argument.bars,
          { row: barRow, colStart: fn.stemCol, colEnd: argument.stemCol, kind: 'app' },
        ],
        barOwners: [...fn.barOwners, ...argument.barOwners, path],
        stems: [
          ...fn.stems,
          ...argument.stems,
          { col: fn.stemCol, rowTop: fn.bottom, rowBottom: barRow, kind: 'output' },
          { col: argument.stemCol, rowTop: argument.bottom, rowBottom: barRow, kind: 'output' },
        ],
        stemOwners: [
          ...fn.stemOwners,
          ...argument.stemOwners,
          fn.occurrences[0]!.path,
          argument.occurrences[0]!.path,
        ],
        free: mergeFree(fn.free, argument.free),
        occurrences: [
          {
            path,
            depth: path.length,
            layoutDepth: binderDepth,
            colStart: 0,
            colEnd: fn.width + argument.width - 1,
            bottom: barRow,
            hit: { kind: 'radial', col: fn.stemCol, rowTop: fn.bottom, rowBottom: barRow },
          },
          ...childHits(fn.occurrences, fn),
          ...childHits(argument.occurrences, argument),
        ],
      }
    }
  }
}

export function trompGrid(term: Term, interfaceArity: number = freeArity(term)): TrompGrid {
  assertWellFormedTerm(term, interfaceArity)
  const box = layoutAt(term, 0, [])
  const slots = Array.from({ length: interfaceArity }, (_, slot) => slot)
  const unusedColumns = new Map<number, number>()
  for (const slot of slots) {
    if (!box.free.has(slot)) unusedColumns.set(slot, box.width + unusedColumns.size)
  }
  const rails: Rail[] = slots.map((slot, index) => {
    const cols = box.free.get(slot)
    const fallbackCol = unusedColumns.get(slot)
    const railCols = cols ?? (fallbackCol === undefined ? [] : [fallbackCol])
    if (railCols.length === 0) throw new Error(`free slot ${slot} has no layout column`)
    return {
      slot,
      row: -(index + 1),
      colStart: Math.min(...railCols),
      colEnd: Math.max(...railCols),
      stemCol: Math.min(...railCols),
    }
  })
  const drops: Stem[] = rails.flatMap((rail) => (
    (box.free.get(rail.slot) ?? []).map((col): Stem => ({
      col,
      rowTop: rail.row,
      rowBottom: 0,
      kind: 'port',
      portSlot: rail.slot,
    }))
  ))
  const output: Stem = {
    col: box.stemCol,
    rowTop: box.bottom,
    rowBottom: box.bottom + 1,
    kind: 'output',
  }
  return {
    cols: box.width + unusedColumns.size,
    rows: box.bottom + 1,
    railRows: rails.length,
    bars: [
      ...box.bars,
      ...rails.map((rail): Bar => ({
        row: rail.row,
        colStart: rail.colStart,
        colEnd: rail.colEnd,
        kind: 'rail',
      })),
    ],
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
