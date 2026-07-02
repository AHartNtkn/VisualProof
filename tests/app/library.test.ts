import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { mkDiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { theoryToJson } from '../../src/kernel/proof/store'
import type { Theorem } from '../../src/kernel/proof/theorem'
import { buildFregeTheory } from '../../src/theories/frege'
import { buildLambdaTheory } from '../../src/theories/lambda'
import { emptyDiagram, addTermNode } from '../../src/app/edit'
import { mkLibrary, loadEntry, unloadEntry, adoptEntry, rebuild } from '../../src/app/library'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)
const fregeJson = () => theoryToJson(buildFregeTheory())
const lambdaJson = () => theoryToJson(buildLambdaTheory())

/** A reflexive theorem (lhs === rhs, zero steps) cites nothing, so it checks
 *  against any context — the minimal adoptable object. */
function trivTheorem(name: string): Theorem {
  const e0 = emptyDiagram()
  const { diagram } = addTermNode(e0, e0.root, p('\\x. x'))
  const dwb = mkDiagramWithBoundary(diagram, [])
  return { name, lhs: dwb, rhs: dwb, steps: [] }
}

describe('mkLibrary', () => {
  it('makes every manifest file available, nothing loaded, no adopted theorems', () => {
    const lib = mkLibrary(['frege.json', 'lambda.json'])
    expect(lib.entries.map((e) => [e.file, e.status])).toEqual([
      ['frege.json', 'available'],
      ['lambda.json', 'available'],
    ])
    expect(lib.adopted).toEqual([])
  })

  it('rebuilds to the empty context when nothing is loaded', () => {
    const boot = rebuild(mkLibrary(['frege.json', 'lambda.json']))
    expect([...boot.ctx.theorems.keys()]).toEqual([])
    expect(boot.constNames.size).toBe(0)
    expect(Object.keys(boot.relations)).toEqual([])
  })
})

describe('loadEntry / rebuild', () => {
  it('loads a manifest file and rebuilds the merged context (theorems + constants + relations)', () => {
    const lib = loadEntry(mkLibrary(['frege.json']), 'frege.json', fregeJson())
    const entry = lib.entries.find((e) => e.file === 'frege.json')!
    expect(entry.status).toBe('loaded')
    const boot = rebuild(lib)
    expect(boot.ctx.theorems.has('plusAssoc')).toBe(true)
    expect(boot.constNames.has('ZERO')).toBe(true)
    expect(boot.relations['nat']).toBeDefined()
  })

  it('loads both shipped files and merges them', () => {
    let lib = mkLibrary(['frege.json', 'lambda.json'])
    lib = loadEntry(lib, 'frege.json', fregeJson())
    lib = loadEntry(lib, 'lambda.json', lambdaJson())
    const boot = rebuild(lib)
    expect(boot.ctx.theorems.has('onePlusOne')).toBe(true)
    expect(boot.ctx.theorems.has('fixedPoint')).toBe(true)
    expect(boot.constNames.has('Y')).toBe(true)
  })

  it('appends a file absent from the manifest as a foreign loaded entry', () => {
    const lib = loadEntry(mkLibrary(['frege.json']), 'mine.json', lambdaJson())
    expect(lib.entries.map((e) => e.file)).toEqual(['frege.json', 'mine.json'])
    expect(lib.entries.find((e) => e.file === 'mine.json')!.status).toBe('loaded')
  })

  it('refuses a duplicate-theorem conflict loudly and leaves the state unchanged', () => {
    const lib = loadEntry(mkLibrary(['frege.json', 'frege2.json']), 'frege.json', fregeJson())
    // loading the same content again under another name duplicates every theorem
    expect(() => loadEntry(lib, 'frege2.json', fregeJson()))
      .toThrowError(/theory merge conflict: duplicate theorem 'plusAssoc'/)
    // caller keeps the prior library: frege2.json is still available, not loaded
    expect(lib.entries.find((e) => e.file === 'frege2.json')!.status).toBe('available')
  })

  it('propagates a malformed-theory refusal from loadTheory (the only road)', () => {
    const bad = { format: 'visual-proof-theory', version: 1, definitions: 'nope', relations: {}, theorems: [] }
    expect(() => loadEntry(mkLibrary(['x.json']), 'x.json', bad)).toThrowError(/malformed theory JSON/)
  })
})

describe('unloadEntry', () => {
  it('returns a manifest file to available and rebuilds from the remainder', () => {
    let lib = mkLibrary(['frege.json', 'lambda.json'])
    lib = loadEntry(lib, 'frege.json', fregeJson())
    lib = loadEntry(lib, 'lambda.json', lambdaJson())
    lib = unloadEntry(lib, 'lambda.json')
    expect(lib.entries.find((e) => e.file === 'lambda.json')!.status).toBe('available')
    const boot = rebuild(lib)
    expect(boot.ctx.theorems.has('plusAssoc')).toBe(true) // frege still loaded
    expect(boot.ctx.theorems.has('fixedPoint')).toBe(false) // lambda gone
    expect(boot.constNames.has('Y')).toBe(false)
  })

  it('drops a foreign (non-manifest) file entirely on unload', () => {
    let lib = loadEntry(mkLibrary(['frege.json']), 'mine.json', lambdaJson())
    lib = unloadEntry(lib, 'mine.json')
    expect(lib.entries.map((e) => e.file)).toEqual(['frege.json'])
  })

  it('refuses to unload a file that is not loaded', () => {
    const lib = mkLibrary(['frege.json'])
    expect(() => unloadEntry(lib, 'frege.json')).toThrowError(/not loaded/)
    expect(() => unloadEntry(lib, 'ghost.json')).toThrowError(/no library entry/)
  })
})

describe('adoptEntry', () => {
  it('records an adopted theorem in its own group and merges it into rebuild', () => {
    let lib = loadEntry(mkLibrary(['frege.json']), 'frege.json', fregeJson())
    lib = adoptEntry(lib, trivTheorem('myLemma'))
    expect(lib.adopted.map((t) => t.name)).toEqual(['myLemma'])
    const boot = rebuild(lib)
    expect(boot.ctx.theorems.has('myLemma')).toBe(true)
    expect(boot.ctx.theorems.has('plusAssoc')).toBe(true) // loaded entry still present
  })

  it('adopts onto an empty library too (no theory loaded)', () => {
    const lib = adoptEntry(mkLibrary([]), trivTheorem('solo'))
    const boot = rebuild(lib)
    expect([...boot.ctx.theorems.keys()]).toEqual(['solo'])
  })

  it('refuses an adopted name that duplicates a loaded theorem, leaving state unchanged', () => {
    const lib = loadEntry(mkLibrary(['frege.json']), 'frege.json', fregeJson())
    expect(() => adoptEntry(lib, trivTheorem('plusAssoc')))
      .toThrowError(/adopted theorem 'plusAssoc' duplicates a loaded theorem/)
    expect(lib.adopted).toEqual([])
  })
})
