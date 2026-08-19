import { describe, expect, it } from 'vitest'
import { SlashController, type SlashCrossing } from '../../src/app/interact/slash'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkEngine } from '../../src/view/engine'
import { LIGHT } from '../../src/view/paint'
import type { PointerSample } from '../../src/app/interact/viewport'
import { place, pointerSample } from './helpers/gesture'
import { segment } from './helpers/build'

function rightSample(point: { x: number; y: number }): PointerSample {
  return { ...pointerSample(point), button: 2 }
}

describe('SlashController', () => {
  function harness() {
    const builder = new DiagramBuilder()
    const seg = segment(builder, builder.root)
    const diagram = builder.build()
    const engine = mkEngine(diagram, [])
    engine.scale = 12
    place(engine, seg.ends[0], { x: 100, y: 300 })
    place(engine, seg.ends[1], { x: 500, y: 300 })
    const commits: SlashCrossing[][] = []
    const stills: PointerSample[] = []
    const refusals: string[] = []
    const controller = new SlashController({
      active: () => true,
      engine: () => engine,
      diagram: () => diagram,
      theme: () => LIGHT,
      commit: (crossings) => { commits.push([...crossings]) },
      still: (sample) => { stills.push(sample) },
      refuse: (text) => { refusals.push(text) },
    })
    return { controller, commits, stills, refusals }
  }

  it('severs the crossed leg', () => {
    const { controller, commits } = harness()
    const claim = controller.claim(rightSample({ x: 300, y: 100 }))
    expect(claim).not.toBeNull()
    claim!.move(rightSample({ x: 300, y: 500 }))
    claim!.release(rightSample({ x: 300, y: 500 }), true)
    expect(commits).toHaveLength(1)
    expect(commits[0]!.length).toBeGreaterThan(0)
  })

  it('a still right-click reaches the resting surface', () => {
    const { controller, stills } = harness()
    const claim = controller.claim(rightSample({ x: 700, y: 700 }))
    claim!.release(rightSample({ x: 700, y: 700 }), false)
    expect(stills).toHaveLength(1)
  })

  it('refuses a slash through nothing', () => {
    const { controller, refusals } = harness()
    const claim = controller.claim(rightSample({ x: 700, y: 650 }))
    claim!.move(rightSample({ x: 720, y: 700 }))
    claim!.release(rightSample({ x: 720, y: 700 }), true)
    expect(refusals).toEqual(['the slash crossed no strand'])
  })
})
