import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { diagramToJson } from '../../../src/kernel/diagram/json'
import { TreeRenderAssetCache } from '../../../src/game/render/assets'
import { DARK } from '../../../src/view/paint'

const blankBuilder = new DiagramBuilder()
const blankDiagram = blankBuilder.build()
const blankJson = JSON.stringify(diagramToJson(blankDiagram))

const doubleBuilder = new DiagramBuilder()
const outer = doubleBuilder.cut(doubleBuilder.root)
doubleBuilder.cut(outer)
const doubleDiagram = doubleBuilder.build()
const doubleJson = JSON.stringify(diagramToJson(doubleDiagram))

describe('tree render asset cache', () => {
  it('derives one immutable render asset for byte-identical diagrams', () => {
    const cache = new TreeRenderAssetCache(DARK)
    const first = cache.get(blankJson, blankDiagram)
    const second = cache.get(blankJson, blankDiagram)

    expect(second).toBe(first)
    expect(first.lods.full.entities.map(({ key }) => key)).toEqual(['b:r0'])
  })

  it('derives a different asset after a real double cut', () => {
    const cache = new TreeRenderAssetCache(DARK)

    expect(cache.get(blankJson, blankDiagram)).not.toBe(cache.get(doubleJson, doubleDiagram))
  })
})
