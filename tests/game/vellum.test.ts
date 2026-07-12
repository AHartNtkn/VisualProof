import { describe, expect, it } from 'vitest'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { exploreForm } from '../../src/kernel/diagram/canonical/explore'
import { blankDiagram, isBlank } from '../../src/game/blank'
import { manifestSeal, dissolveSeal } from '../../src/game/vellum'
import { minimalPuzzle } from './catalog-fixture'

const seal = minimalPuzzle({ name: { professional: 'Two Veils' } })

describe('exact solved-seal vellums', () => {
  it('manifests one whole closed seal in a chosen region', () => {
    const manifested = manifestSeal(blankDiagram(), blankDiagram().root, seal)
    expect(exploreForm(manifested)).toBe(exploreForm(seal.goal.diagram))
  })

  it('dissolves only an exact whole occurrence', () => {
    const manifested = manifestSeal(blankDiagram(), blankDiagram().root, seal)
    const outer = Object.entries(manifested.regions)
      .find(([, region]) => region.kind === 'cut' && region.parent === manifested.root)![0]
    const selection = mkSelection(manifested, { region: manifested.root, regions: [outer], nodes: [], wires: [] })
    expect(isBlank(dissolveSeal(manifested, selection, seal))).toBe(true)
  })

  it('refuses a strict subgraph and leaves the caller-owned diagram unchanged', () => {
    const manifested = manifestSeal(blankDiagram(), blankDiagram().root, seal)
    const outer = Object.entries(manifested.regions)
      .find(([, region]) => region.kind === 'cut' && region.parent === manifested.root)![0]
    const inner = Object.entries(manifested.regions)
      .find(([, region]) => region.kind === 'cut' && region.parent === outer)![0]
    const selection = mkSelection(manifested, { region: outer, regions: [inner], nodes: [], wires: [] })
    const before = exploreForm(manifested)
    expect(() => dissolveSeal(manifested, selection, seal)).toThrow(/not an exact occurrence/)
    expect(exploreForm(manifested)).toBe(before)
  })
})
