import { describe, expect, it } from 'vitest'
import {
  defineEntry,
  emptyLibrary,
  loadEntry,
  rebuild,
  reconcile,
  unloadEntry,
} from '../../src/app/library'
import { theoryToJson } from '../../src/kernel/proof/store'
import { tinyTheory, unaryDefinition } from '../fixtures/zero-signature'

describe('generic theory library', () => {
  it('loads, rebuilds, and unloads a zero-signature theory', () => {
    const available = reconcile(emptyLibrary(), ['tiny.json'])
    const loaded = loadEntry(available, 'tiny.json', theoryToJson(tinyTheory()))
    expect([...rebuild(loaded).ctx.relations.keys()]).toEqual(['UnaryWitness'])
    const unloaded = unloadEntry(loaded, 'tiny.json')
    expect(unloaded.entries).toEqual([{ file: 'tiny.json', status: 'available' }])
    expect(rebuild(unloaded).ctx.relations.size).toBe(0)
  })

  it('keeps session definitions in the same conflict-checked namespace', () => {
    const defined = defineEntry(emptyLibrary(), 'LocalUnary', unaryDefinition())
    expect([...rebuild(defined).ctx.relations.keys()]).toEqual(['LocalUnary'])
    expect(() => defineEntry(defined, 'LocalUnary', unaryDefinition())).toThrow(/duplicates/)
  })
})
