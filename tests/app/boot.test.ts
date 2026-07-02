import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { verifyTheory, loadTheory, theoryToJson } from '../../src/kernel/proof/store'
import { buildFregeTheory } from '../../src/theories/frege'
import { fetchManifest, mergeTheories } from '../../src/app/boot'
import { inMemoryTheoryReader } from './boot-fixture'

const noConsts = new Set<string>()
const pp = (s: string) => parseTerm(s, noConsts)

describe('fetchManifest', () => {
  it('reads ONLY the manifest — the list of available files, nothing else', async () => {
    const seen: string[] = []
    const real = inMemoryTheoryReader()
    const spy = (url: string): Promise<unknown> => {
      seen.push(url)
      return real(url)
    }
    const manifest = await fetchManifest(spy)
    expect(manifest).toEqual(['frege.json', 'lambda.json'])
    // no theory content is fetched at boot: the manifest URL is the only read
    expect(seen).toEqual(['theories/index.json'])
  })

  it('refuses a missing manifest loudly', async () => {
    const reader = (url: string): Promise<unknown> =>
      Promise.reject(new Error(`no file at '${url}'`))
    await expect(fetchManifest(reader)).rejects.toThrow(/no file at 'theories\/index\.json'/)
  })

  it('refuses a non-array manifest loudly', async () => {
    const reader = (url: string): Promise<unknown> =>
      url === 'theories/index.json' ? Promise.resolve({ frege: 'frege.json' }) : Promise.reject(new Error('unused'))
    await expect(fetchManifest(reader)).rejects.toThrow(/must be a JSON array of file-name strings/)
  })

  it('refuses a manifest whose entries are not all strings', async () => {
    const reader = (url: string): Promise<unknown> =>
      url === 'theories/index.json' ? Promise.resolve(['frege.json', 42]) : Promise.reject(new Error('unused'))
    await expect(fetchManifest(reader)).rejects.toThrow(/must be a JSON array of file-name strings/)
  })
})

describe('mergeTheories', () => {
  it('merges disjoint bundles: theorems citable, constants unioned, relation present', () => {
    const frege = loadTheory(theoryToJson(buildFregeTheory()))
    const merged = mergeTheories([frege])
    expect(merged.ctx.theorems.has('plusAssoc')).toBe(true)
    for (const name of ['ZERO', 'SUCC', 'PLUS', 'ONE']) {
      expect(merged.constNames.has(name)).toBe(true)
    }
    expect(merged.relations['nat']).toBeDefined()
  })

  it('empty input rebuilds to the empty context (the honest empty boot)', () => {
    const merged = mergeTheories([])
    expect([...merged.ctx.theorems.keys()]).toEqual([])
    expect(merged.constNames.size).toBe(0)
    expect(Object.keys(merged.relations)).toEqual([])
  })

  it('refuses conflicting definition bodies loudly', () => {
    const frege = buildFregeTheory()
    const loaded = loadTheory(JSON.parse(JSON.stringify(theoryToJson(frege))))
    const conflicting = {
      theory: { definitions: { ONE: pp('\\f. \\x. x') }, relations: {}, theorems: [] },
      ctx: verifyTheory({ definitions: { ONE: pp('\\f. \\x. x') }, relations: {}, theorems: [] }),
    }
    expect(() => mergeTheories([loaded, conflicting]))
      .toThrowError(/theory merge conflict: definition 'ONE'/)
  })
})
