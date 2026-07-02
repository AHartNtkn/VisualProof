import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { mkDiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { theoryToJson } from '../../src/kernel/proof/store'
import type { Theorem } from '../../src/kernel/proof/theorem'
import { buildFregeTheory } from '../../src/theories/frege'
import { buildLambdaTheory } from '../../src/theories/lambda'
import { emptyDiagram, addTermNode } from '../../src/app/edit'
import type { LibraryEntry } from '../../src/app/library'
import { emptyLibrary, reconcile, loadEntry, unloadEntry, adoptEntry, rebuild } from '../../src/app/library'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)
const fregeJson = () => theoryToJson(buildFregeTheory())
const lambdaJson = () => theoryToJson(buildLambdaTheory())
const status = (entries: readonly LibraryEntry[]) => entries.map((e) => [e.file, e.status])

/** A reflexive theorem (lhs === rhs, zero steps) cites nothing, so it checks
 *  against any context — the minimal adoptable object. */
function trivTheorem(name: string): Theorem {
  const e0 = emptyDiagram()
  const { diagram } = addTermNode(e0, e0.root, p('\\x. x'))
  const dwb = mkDiagramWithBoundary(diagram, [])
  return { name, lhs: dwb, rhs: dwb, steps: [] }
}

describe('emptyLibrary', () => {
  it('knows nothing: no folder, no entries, no adopted; rebuilds to the empty context', () => {
    const lib = emptyLibrary()
    expect(lib.folder).toEqual([])
    expect(lib.entries).toEqual([])
    expect(lib.adopted).toEqual([])
    const boot = rebuild(lib)
    expect([...boot.ctx.theorems.keys()]).toEqual([])
    expect(boot.constNames.size).toBe(0)
    expect(Object.keys(boot.relations)).toEqual([])
  })
})

describe('reconcile (Open folder / Refresh)', () => {
  it('lists every folder file as available, uniformly, and records the folder', () => {
    const lib = reconcile(emptyLibrary(), ['frege.json', 'lambda.json'])
    expect(lib.folder).toEqual(['frege.json', 'lambda.json'])
    expect(status(lib.entries)).toEqual([
      ['frege.json', 'available'],
      ['lambda.json', 'available'],
    ])
  })

  it('preserves a loaded entry across a refresh and lists the rest available', () => {
    let lib = reconcile(emptyLibrary(), ['frege.json', 'lambda.json'])
    lib = loadEntry(lib, 'frege.json', fregeJson())
    lib = reconcile(lib, ['frege.json', 'lambda.json']) // refresh
    expect(status(lib.entries)).toEqual([
      ['frege.json', 'loaded'],
      ['lambda.json', 'available'],
    ])
  })

  it('drops an available file that has disappeared from the folder', () => {
    let lib = reconcile(emptyLibrary(), ['frege.json', 'lambda.json'])
    lib = reconcile(lib, ['frege.json']) // lambda.json removed on disk
    expect(status(lib.entries)).toEqual([['frege.json', 'available']])
  })

  it('keeps a one-off loaded file even when it is not in the folder', () => {
    let lib = loadEntry(emptyLibrary(), 'mine.json', lambdaJson()) // opened directly, no folder
    lib = reconcile(lib, ['frege.json']) // then a folder is opened
    expect(status(lib.entries)).toEqual([
      ['frege.json', 'available'],
      ['mine.json', 'loaded'],
    ])
  })
})

describe('loadEntry / rebuild', () => {
  it('flips a folder file to loaded and merges its content into rebuild', () => {
    let lib = reconcile(emptyLibrary(), ['frege.json'])
    lib = loadEntry(lib, 'frege.json', fregeJson())
    expect(lib.entries.find((e) => e.file === 'frege.json')!.status).toBe('loaded')
    const boot = rebuild(lib)
    expect(boot.ctx.theorems.has('plusAssoc')).toBe(true)
    expect(boot.constNames.has('ZERO')).toBe(true)
    expect(boot.relations['nat']).toBeDefined()
  })

  it('appends a directly-opened file (not in any folder) as a loaded entry', () => {
    const lib = loadEntry(emptyLibrary(), 'mine.json', lambdaJson())
    expect(status(lib.entries)).toEqual([['mine.json', 'loaded']])
    expect(rebuild(lib).ctx.theorems.has('fixedPoint')).toBe(true)
  })

  it('refuses a duplicate-theorem conflict loudly and leaves the state unchanged', () => {
    const lib = loadEntry(reconcile(emptyLibrary(), ['frege.json', 'frege2.json']), 'frege.json', fregeJson())
    expect(() => loadEntry(lib, 'frege2.json', fregeJson()))
      .toThrowError(/theory merge conflict: duplicate theorem 'plusAssoc'/)
    expect(lib.entries.find((e) => e.file === 'frege2.json')!.status).toBe('available')
  })

  it('propagates a malformed-theory refusal from loadTheory (the only road)', () => {
    const bad = { format: 'visual-proof-theory', version: 1, definitions: 'nope', relations: {}, theorems: [] }
    expect(() => loadEntry(emptyLibrary(), 'x.json', bad)).toThrowError(/malformed theory JSON/)
  })
})

describe('unloadEntry', () => {
  it('returns a folder file to available and rebuilds from the remainder', () => {
    let lib = reconcile(emptyLibrary(), ['frege.json', 'lambda.json'])
    lib = loadEntry(lib, 'frege.json', fregeJson())
    lib = loadEntry(lib, 'lambda.json', lambdaJson())
    lib = unloadEntry(lib, 'lambda.json')
    expect(lib.entries.find((e) => e.file === 'lambda.json')!.status).toBe('available')
    const boot = rebuild(lib)
    expect(boot.ctx.theorems.has('plusAssoc')).toBe(true) // frege still loaded
    expect(boot.ctx.theorems.has('fixedPoint')).toBe(false) // lambda gone
    expect(boot.constNames.has('Y')).toBe(false)
  })

  it('drops a directly-opened (non-folder) file entirely on unload', () => {
    let lib = loadEntry(emptyLibrary(), 'mine.json', lambdaJson())
    lib = unloadEntry(lib, 'mine.json')
    expect(lib.entries).toEqual([])
  })

  it('refuses to unload a file that is not loaded', () => {
    const lib = reconcile(emptyLibrary(), ['frege.json'])
    expect(() => unloadEntry(lib, 'frege.json')).toThrowError(/not loaded/)
    expect(() => unloadEntry(lib, 'ghost.json')).toThrowError(/no library entry/)
  })
})

describe('adoptEntry', () => {
  it('records an adopted theorem in its own group and merges it into rebuild', () => {
    let lib = loadEntry(emptyLibrary(), 'frege.json', fregeJson())
    lib = adoptEntry(lib, trivTheorem('myLemma'))
    expect(lib.adopted.map((t) => t.name)).toEqual(['myLemma'])
    const boot = rebuild(lib)
    expect(boot.ctx.theorems.has('myLemma')).toBe(true)
    expect(boot.ctx.theorems.has('plusAssoc')).toBe(true)
  })

  it('adopts onto an empty library too (no file loaded)', () => {
    const lib = adoptEntry(emptyLibrary(), trivTheorem('solo'))
    expect([...rebuild(lib).ctx.theorems.keys()]).toEqual(['solo'])
  })

  it('refuses an adopted name that duplicates a loaded theorem, leaving state unchanged', () => {
    const lib = loadEntry(emptyLibrary(), 'frege.json', fregeJson())
    expect(() => adoptEntry(lib, trivTheorem('plusAssoc')))
      .toThrowError(/adopted theorem 'plusAssoc' duplicates a loaded theorem/)
    expect(lib.adopted).toEqual([])
  })
})
