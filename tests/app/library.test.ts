import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { mkDiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { theoryToJson } from '../../src/kernel/proof/store'
import type { Theorem } from '../../src/kernel/proof/theorem'
import { buildFregeTheory } from '../../src/theories/frege'
import { buildLambdaTheory } from '../../src/theories/lambda'
import type { DiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { emptyDiagram, addTermNode } from '../../src/app/edit'
import type { LibraryEntry } from '../../src/app/library'
import { emptyLibrary, reconcile, loadEntry, unloadEntry, adoptEntry, defineEntry, rebuild } from '../../src/app/library'

const p = (s: string) => parseTerm(s)
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

/** A closed arity-1 relation body (one term node, its free-var line the
 *  boundary). No ref nodes, so its refs resolve against any context. */
function trivRelation(): DiagramWithBoundary {
  const e0 = emptyDiagram()
  const { diagram, node } = addTermNode(e0, e0.root, p('y'))
  const bound = Object.keys(diagram.wires).find((w) =>
    diagram.wires[w]!.endpoints.some((ep) => ep.node === node && ep.port.kind === 'freeVar'),
  )!
  return mkDiagramWithBoundary(diagram, [bound])
}

describe('emptyLibrary', () => {
  it('knows nothing: no folder, no entries, no adopted; rebuilds to the empty context', () => {
    const lib = emptyLibrary()
    expect(lib.folder).toEqual([])
    expect(lib.entries).toEqual([])
    expect(lib.adopted).toEqual([])
    const boot = rebuild(lib)
    expect([...boot.ctx.theorems.keys()]).toEqual([])
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
    const bad = { format: 'visual-proof-theory', version: 1, relations: 'nope', theorems: [] }
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

describe('defineEntry', () => {
  it('records a defined relation in its group and merges it into ctx.relations and the record', () => {
    let lib = loadEntry(emptyLibrary(), 'frege.json', fregeJson())
    lib = defineEntry(lib, 'myRel', trivRelation())
    expect(lib.definedRelations.map((r) => r.name)).toEqual(['myRel'])
    const boot = rebuild(lib)
    expect(boot.ctx.relations.has('myRel')).toBe(true)
    expect(boot.relations['myRel']).toBeDefined()
    expect(boot.relations['nat']).toBeDefined() // loaded relation still present
  })

  it('defines onto an empty library too (no file loaded)', () => {
    const lib = defineEntry(emptyLibrary(), 'solo', trivRelation())
    expect(Object.keys(rebuild(lib).relations)).toEqual(['solo'])
  })

  it('survives unloading an unrelated file — the defined relation persists across rebuild', () => {
    let lib = loadEntry(emptyLibrary(), 'frege.json', fregeJson())
    lib = defineEntry(lib, 'myRel', trivRelation())
    lib = unloadEntry(lib, 'frege.json') // folder-less open → dropped
    const boot = rebuild(lib)
    expect(boot.relations['myRel']).toBeDefined()
    expect(boot.relations['nat']).toBeUndefined() // frege gone
  })

  it('refuses a defined name that duplicates a loaded relation, leaving state unchanged', () => {
    const lib = loadEntry(emptyLibrary(), 'frege.json', fregeJson())
    expect(() => defineEntry(lib, 'nat', trivRelation()))
      .toThrowError(/defined relation 'nat' duplicates a loaded or defined relation/)
    expect(lib.definedRelations).toEqual([])
  })

  it('refuses a defined name that duplicates a loaded theorem (one namespace)', () => {
    const lib = loadEntry(emptyLibrary(), 'frege.json', fregeJson())
    expect(() => defineEntry(lib, 'plusAssoc', trivRelation()))
      .toThrowError(/defined relation 'plusAssoc' duplicates a theorem name/)
    expect(lib.definedRelations).toEqual([])
  })

  it('refuses adopting a theorem whose name collides with a defined relation', () => {
    const lib = defineEntry(emptyLibrary(), 'shared', trivRelation())
    expect(() => adoptEntry(lib, trivTheorem('shared')))
      .toThrowError(/adopted theorem 'shared' duplicates a loaded theorem or a relation/)
  })
})
