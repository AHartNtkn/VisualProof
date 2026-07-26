import { describe, expect, it } from 'vitest'
import { emptyLibrary, loadEntry, rebuild } from '../../src/app/library'
import { sessionTheory } from '../../src/app/persist'
import { mkReplay } from '../../src/app/replay'
import { loadTheory, theoryToJson } from '../../src/kernel/proof/store'
import { tinyTheory } from '../fixtures/zero-signature'

describe('load, use, and save pipeline', () => {
  it('keeps the same structural authority through library and persistence', () => {
    const library = loadEntry(emptyLibrary(), 'tiny.json', theoryToJson(tinyTheory()))
    const boot = rebuild(library)
    const replay = mkReplay('StructuralReflexivity', boot.ctx)
    expect(replay.actionCount).toBe(0)
    const saved = sessionTheory(boot.ctx, { relations: boot.relations })
    expect([...loadTheory(theoryToJson(saved)).ctx.relations.keys()]).toEqual(['UnaryWitness'])
  })
})
