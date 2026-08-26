import { describe, expect, it } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { trompGrid } from '../../src/view/tromp'

const p = (source: string) => parseTerm(source).term

describe('trompGrid', () => {
  it('lays out the identity with one binder bar, one variable stem, and one output', () => {
    const grid = trompGrid(p('\\x. x'))

    expect(grid.cols).toBe(1)
    expect(grid.railRows).toBe(0)
    expect(grid.bars).toEqual([{ row: 0, colStart: 0, colEnd: 0, kind: 'lam' }])
    expect(grid.stems).toContainEqual({ col: 0, rowTop: 0, rowBottom: 1, kind: 'var' })
    expect(grid.stems).toContainEqual({ col: 0, rowTop: 1, rowBottom: 2, kind: 'output' })
    expect(grid.outputCol).toBe(0)
  })

  it('stacks binder bars by depth and hangs each variable from its binder', () => {
    const grid = trompGrid(p('\\x. \\y. x'))

    expect(grid.bars).toContainEqual({ row: 0, colStart: 0, colEnd: 0, kind: 'lam' })
    expect(grid.bars).toContainEqual({ row: 1, colStart: 0, colEnd: 0, kind: 'lam' })
    expect(grid.stems).toContainEqual({ col: 0, rowTop: 0, rowBottom: 2, kind: 'var' })
  })

  it('joins an application one row below the deeper side', () => {
    const grid = trompGrid(p('(\\x. x) (\\x. x)'))

    expect(grid.cols).toBe(2)
    expect(grid.bars).toContainEqual({ row: 2, colStart: 0, colEnd: 1, kind: 'app' })
    expect(grid.stems).toContainEqual({ col: 0, rowTop: 1, rowBottom: 2, kind: 'output' })
    expect(grid.stems).toContainEqual({ col: 1, rowTop: 1, rowBottom: 2, kind: 'output' })
    expect(grid.outputCol).toBe(0)
  })

  it('gives each numeric free slot one rail in first-occurrence slot order', () => {
    const grid = trompGrid(p('y (z y)'))

    expect(grid.railRows).toBe(2)
    const yRail = grid.rails.find((rail) => rail.slot === 0)!
    const zRail = grid.rails.find((rail) => rail.slot === 1)!
    expect(yRail.row).toBe(-1)
    expect(zRail.row).toBe(-2)
    expect(yRail.colStart).toBe(0)
    expect(yRail.colEnd).toBe(2)
    expect(grid.stems.filter((stem) => stem.kind === 'port' && stem.portSlot === 0 && stem.rowTop === -1)).toHaveLength(2)
  })

  it('keeps every stem and bar inside the declared grid bounds', () => {
    const grid = trompGrid(p('\\f. \\x. f (f (f x))'))
    for (const bar of grid.bars) {
      expect(bar.colStart).toBeGreaterThanOrEqual(0)
      expect(bar.colEnd).toBeLessThan(grid.cols)
      expect(bar.row).toBeGreaterThanOrEqual(-grid.railRows)
      expect(bar.row).toBeLessThan(grid.rows)
    }
    for (const stem of grid.stems) {
      expect(stem.col).toBeGreaterThanOrEqual(0)
      expect(stem.col).toBeLessThan(grid.cols)
      expect(stem.rowTop).toBeLessThanOrEqual(stem.rowBottom)
      expect(stem.rowBottom).toBeLessThanOrEqual(grid.rows)
    }
  })

  it('does not overlap two bars on the same row', () => {
    const grid = trompGrid(p('(\\x. x x) (\\y. y) (z z)'))
    const byRow = new Map<number, { start: number; end: number }[]>()
    for (const bar of grid.bars) {
      const peers = byRow.get(bar.row) ?? []
      for (const peer of peers) {
        expect(bar.colStart > peer.end || bar.colEnd < peer.start).toBe(true)
      }
      peers.push({ start: bar.colStart, end: bar.colEnd })
      byRow.set(bar.row, peers)
    }
  })

  it('retains one interaction occurrence for every exact structural path', () => {
    const grid = trompGrid(p('a ((\\x. x) b)'))

    expect(grid.occurrences.map((occurrence) => occurrence.path)).toEqual([
      [],
      ['fn'],
      ['argument'],
      ['argument', 'fn'],
      ['argument', 'fn', 'body'],
      ['argument', 'argument'],
    ])
  })

  it('keeps repeated equal subterms distinct by occurrence path', () => {
    const grid = trompGrid(p('(\\x. x) (\\x. x)'))

    expect(grid.occurrences.map((occurrence) => occurrence.path)).toContainEqual(['fn'])
    expect(grid.occurrences.map((occurrence) => occurrence.path)).toContainEqual(['argument'])
  })

  it('records structural ownership for every painted bar and stem', () => {
    const grid = trompGrid(p('a ((\\x. x) b)'))

    expect(grid.barOwners).toHaveLength(grid.bars.length)
    expect(grid.stemOwners).toHaveLength(grid.stems.length)
    expect(grid.barOwners).toContainEqual(['argument', 'fn'])
    expect(grid.stemOwners).toContainEqual(['argument', 'fn', 'body'])
    expect(grid.stemOwners).toContainEqual([])
  })

  it('produces exactly equal geometry for alpha-equivalent parsed inputs', () => {
    expect(trompGrid(p('\\x. x free'))).toEqual(trompGrid(p('\\renamed. renamed other')))
  })
})
