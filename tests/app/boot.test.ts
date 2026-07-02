import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { verifyTheory, loadTheory, theoryToJson } from '../../src/kernel/proof/store'
import { buildFregeTheory } from '../../src/theories/frege'
import { fetchBootContext, mergeTheories } from '../../src/app/boot'
import { inMemoryTheoryReader } from './boot-fixture'

const noConsts = new Set<string>()
const pp = (s: string) => parseTerm(s, noConsts)

describe('fetchBootContext', () => {
  it('loads the shipped manifest + files and merges: theorems citable, constants unioned, nat relation present', async () => {
    const boot = await fetchBootContext(inMemoryTheoryReader())
    expect([...boot.ctx.theorems.keys()].sort()).toEqual(
      ['fixedPoint', 'onePlusOne', 'plusAssoc', 'plusLeftUnit', 'plusRightUnit', 'succShiftS', 'plusComm'].sort(),
    )
    for (const name of ['ZERO', 'SUCC', 'PLUS', 'ONE', 'TWO', 'Y']) {
      expect(boot.constNames.has(name)).toBe(true)
    }
    expect(boot.relations['nat']).toBeDefined()
  })

  it('loads each manifest file through loadTheory in manifest order (the merge order)', async () => {
    const seen: string[] = []
    const real = inMemoryTheoryReader()
    const spy = (url: string): Promise<unknown> => {
      seen.push(url)
      return real(url)
    }
    await fetchBootContext(spy)
    expect(seen).toEqual(['theories/index.json', 'theories/frege.json', 'theories/lambda.json'])
  })

  it('refuses a missing manifest loudly', async () => {
    const reader = (url: string): Promise<unknown> =>
      Promise.reject(new Error(`no file at '${url}'`))
    await expect(fetchBootContext(reader)).rejects.toThrow(/no file at 'theories\/index\.json'/)
  })

  it('refuses a non-array manifest loudly', async () => {
    const reader = (url: string): Promise<unknown> =>
      url === 'theories/index.json' ? Promise.resolve({ frege: 'frege.json' }) : Promise.reject(new Error('unused'))
    await expect(fetchBootContext(reader)).rejects.toThrow(/must be a JSON array of file-name strings/)
  })

  it('propagates a corrupted theory file refusal from loadTheory (no silent skip)', async () => {
    const real = inMemoryTheoryReader()
    const reader = (url: string): Promise<unknown> => {
      if (url === 'theories/frege.json') return Promise.resolve({ format: 'visual-proof-theory', version: 1, definitions: 'nope', relations: {}, theorems: [] })
      return real(url)
    }
    await expect(fetchBootContext(reader)).rejects.toThrow(/malformed theory JSON/)
  })
})

describe('mergeTheories', () => {
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
