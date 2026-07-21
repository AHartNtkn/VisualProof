import { describe, expect, it } from 'vitest'
import { loadGameContent } from '../../src/game/catalog'
import { gameContentFiles } from '../../src/game/content/files'
import { analyzeSeyricStart } from '../../src/game/content/seyric-authority'
import { puzzleId } from '../../src/game/types'

const catalog = loadGameContent(gameContentFiles)

const transitivelyDependsOn = (start: string, required: string): boolean => {
  const pending = [...catalog.placement(puzzleId(start)).prerequisites]
  const visited = new Set<string>()
  while (pending.length > 0) {
    const current = pending.pop()!
    if (current === required) return true
    if (visited.has(current)) continue
    visited.add(current)
    pending.push(...catalog.placement(puzzleId(current)).prerequisites)
  }
  return false
}

describe('culture progression coherence', () => {
  it('assigns every Seyric-form start to Seyric and none to Myratic', () => {
    const seyric = catalog.puzzlesInCulture('seyric-horizon' as never)
    const myratic = catalog.puzzlesInCulture('myratic-tradition' as never)

    expect(seyric).toEqual(expect.arrayContaining([
      puzzleId('empty-ring-release'),
      puzzleId('nested-owner-introduction'),
    ]))
    expect(myratic.filter((id) => analyzeSeyricStart(catalog.puzzle(id).diagram).ok)).toEqual([])
  })

  it('keeps the foundational Seyric instruction chain ahead of the Myratic gateway', () => {
    expect(catalog.placement(puzzleId('empty-ring-release')).prerequisites)
      .toEqual([puzzleId('echoed-veil')])
    expect(catalog.placement(puzzleId('single-mark-return')).prerequisites)
      .toEqual([puzzleId('empty-ring-release')])
    expect(catalog.placement(puzzleId('nested-owner-introduction')).prerequisites)
      .toEqual([puzzleId('single-mark-return')])
    expect(catalog.culture('myratic-tradition' as never).unlocksAfter)
      .toEqual([puzzleId('nested-owner-introduction')])
  })

  it('gates every later multi-owner Seyric puzzle on the nested-owner introduction', () => {
    const missing = catalog.puzzlesInCulture('seyric-horizon' as never).flatMap((id) => {
      const analysis = analyzeSeyricStart(catalog.puzzle(id).diagram)
      if (id === puzzleId('nested-owner-introduction') || analysis.prefix.length < 2) return []
      return transitivelyDependsOn(id, 'nested-owner-introduction') ? [] : [id]
    })

    expect(missing).toEqual([])
  })
})
