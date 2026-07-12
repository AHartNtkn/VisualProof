import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { trompGrid } from '../../src/view/tromp'

const p = (s: string) => parseTerm(s)

describe('trompGrid', () => {
  it('lays out the identity: one binder bar, one stem, one output', () => {
    const g = trompGrid(p('\\x. x'))
    expect(g.cols).toBe(1)
    expect(g.railRows).toBe(0)
    expect(g.bars).toEqual([{ row: 0, colStart: 0, colEnd: 0, kind: 'lam' }])
    // the variable stem hangs from the row-0 bar; the output exits below
    expect(g.stems).toContainEqual({ col: 0, rowTop: 0, rowBottom: 1, kind: 'var' })
    expect(g.stems).toContainEqual({ col: 0, rowTop: 1, rowBottom: 2, kind: 'output' })
    expect(g.outputCol).toBe(0)
  })

  it('stacks binder bars by depth and hangs each variable from its own binder', () => {
    const g = trompGrid(p('\\x. \\y. x'))
    expect(g.bars).toContainEqual({ row: 0, colStart: 0, colEnd: 0, kind: 'lam' })
    expect(g.bars).toContainEqual({ row: 1, colStart: 0, colEnd: 0, kind: 'lam' })
    // x is bound by the OUTER binder (row 0), entered at depth 2
    expect(g.stems).toContainEqual({ col: 0, rowTop: 0, rowBottom: 2, kind: 'var' })
  })

  it('an application joins the two output stems with a bar one row below the deeper side', () => {
    const g = trompGrid(p('(\\x. x) (\\x. x)'))
    expect(g.cols).toBe(2)
    // both identity boxes bottom out at row 1; the app bar sits at row 2
    expect(g.bars).toContainEqual({ row: 2, colStart: 0, colEnd: 1, kind: 'app' })
    expect(g.stems).toContainEqual({ col: 0, rowTop: 1, rowBottom: 2, kind: 'output' })
    expect(g.stems).toContainEqual({ col: 1, rowTop: 1, rowBottom: 2, kind: 'output' })
    expect(g.outputCol).toBe(0) // the function side carries the result
  })

  it('gives every distinct free port one rail above row 0, in first-occurrence order', () => {
    const g = trompGrid(p('y (z y)'))
    expect(g.railRows).toBe(2)
    const yRail = g.rails.find((r) => r.name === 'y')!
    const zRail = g.rails.find((r) => r.name === 'z')!
    expect(yRail.row).toBe(-1) // first occurrence
    expect(zRail.row).toBe(-2)
    // y occurs at columns 0 and 2: its rail spans them, with a drop at each
    expect(yRail.colStart).toBe(0)
    expect(yRail.colEnd).toBe(2)
    expect(g.stems.filter((s) => s.kind === 'port' && s.portName === 'y' && s.rowTop === -1)).toHaveLength(2)
  })

  it('every stem and bar stays inside the declared grid bounds', () => {
    const g = trompGrid(p('\\f. \\x. f (f (f x))'))
    for (const b of g.bars) {
      expect(b.colStart).toBeGreaterThanOrEqual(0)
      expect(b.colEnd).toBeLessThan(g.cols)
      expect(b.row).toBeGreaterThanOrEqual(-g.railRows)
      expect(b.row).toBeLessThan(g.rows)
    }
    for (const s of g.stems) {
      expect(s.col).toBeGreaterThanOrEqual(0)
      expect(s.col).toBeLessThan(g.cols)
      expect(s.rowTop).toBeLessThanOrEqual(s.rowBottom)
      expect(s.rowBottom).toBeLessThanOrEqual(g.rows)
    }
  })

  it('no two bars overlap on the same row', () => {
    const g = trompGrid(p('(\\x. x x) (\\y. y) (z z)'))
    const byRow = new Map<number, { s: number; e: number }[]>()
    for (const b of g.bars) {
      const list = byRow.get(b.row) ?? []
      for (const o of list) {
        expect(b.colStart > o.e || b.colEnd < o.s).toBe(true)
      }
      list.push({ s: b.colStart, e: b.colEnd })
      byRow.set(b.row, list)
    }
  })

  it('retains one interaction occurrence for every exact syntactic path', () => {
    const g = trompGrid(p('a ((\\x. x) b)'))
    expect(g.occurrences.map((occurrence) => occurrence.path)).toEqual([
      [],
      ['fn'],
      ['arg'],
      ['arg', 'fn'],
      ['arg', 'fn', 'body'],
      ['arg', 'arg'],
    ])
  })

  it('keeps repeated equal subterms distinct by occurrence path', () => {
    const g = trompGrid(p('(\\x. x) (\\x. x)'))
    expect(g.occurrences.map((occurrence) => occurrence.path)).toContainEqual(['fn'])
    expect(g.occurrences.map((occurrence) => occurrence.path)).toContainEqual(['arg'])
    expect(g.occurrences.find((occurrence) => occurrence.path.join('/') === 'fn')?.depth).toBe(1)
    expect(g.occurrences.find((occurrence) => occurrence.path.join('/') === 'arg')?.depth).toBe(1)
  })

  it('records syntax ownership for every painted bar and stem instead of reconstructing it later', () => {
    const g = trompGrid(p('a ((\\x. x) b)'))
    expect(g.barOwners).toHaveLength(g.bars.length)
    expect(g.stemOwners).toHaveLength(g.stems.length)
    expect(g.barOwners).toContainEqual(['arg', 'fn'])
    expect(g.stemOwners).toContainEqual(['arg', 'fn', 'body'])
    expect(g.stemOwners).toContainEqual([])
  })
})
