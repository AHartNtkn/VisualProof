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

describe('tree render assets', () => {
  it('derives a complete full-detail representation from a generic diagram', () => {
    const cache = new TreeRenderAssetCache(DARK)
    const asset = cache.get(blankJson, blankDiagram)

    expect(asset.lods.full.entities.map(({ key }) => key)).toEqual(['b:r0'])
    expect(asset.bounds.radius).toBeGreaterThan(0)
    expect(asset.lods.marker.size).toBeGreaterThan(0)
  })

  it('represents the branches created by a real double cut', () => {
    const cache = new TreeRenderAssetCache(DARK)
    const before = cache.get(blankJson, blankDiagram)
    const after = cache.get(doubleJson, doubleDiagram)

    expect(before.lods.full.entities.map(({ key }) => key)).toEqual(['b:r0'])
    expect(after.lods.full.entities.map(({ key }) => key)).toEqual(['b:r0', 'b:r1', 'b:r2'])
  })
})
