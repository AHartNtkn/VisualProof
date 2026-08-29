import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest'
import { formulaToDiagram } from '../../src/formula'
import { scene3 } from '../../src/view3d/scene'
import { SCENE_TWEEN_MS, SceneTweenTrack, type FadedEntity } from '../../src/view3d/transition'

const renderState = vi.hoisted(() => ({
  entityFrames: [] as Array<readonly FadedEntity[]>,
}))

vi.mock('../../src/view3d/render', () => ({
  mountRender: () => ({
    setEntities: (entities: readonly FadedEntity[]) => {
      renderState.entityFrames.push(entities)
    },
    setTheme: () => {},
    setPose: () => {},
    setHoverKeys: () => {},
    pickAt: () => null,
    render: () => {},
    resize: () => {},
    dispose: () => {},
  }),
}))

import { mountView3 } from '../../src/view3d'
import { DARK } from '../../src/view/paint'

type FrameRequestCallback = (time: number) => void

class TestResizeObserver {
  public observe(): void {}
  public disconnect(): void {}
}

const container = (): HTMLElement => ({
  clientWidth: 800,
  clientHeight: 600,
  dataset: {},
  addEventListener: () => {},
  removeEventListener: () => {},
} as unknown as HTMLElement)

describe('mountView3 diagram transitions', () => {
  let now = 0
  let frames: FrameRequestCallback[] = []

  beforeEach(() => {
    now = 0
    frames = []
    renderState.entityFrames.length = 0
    vi.stubGlobal('ResizeObserver', TestResizeObserver)
    vi.stubGlobal('requestAnimationFrame', (callback: FrameRequestCallback) => {
      frames.push(callback)
      return frames.length
    })
    vi.spyOn(performance, 'now').mockImplementation(() => now)
  })

  afterEach(() => {
    vi.restoreAllMocks()
    vi.unstubAllGlobals()
  })

  const runFrame = (time: number): void => {
    now = time
    const callback = frames.shift()
    if (callback === undefined) throw new Error(`no animation frame queued at ${time}`)
    callback(time)
  }

  it('restarts an interrupted diagram update from the displayed shared-track scene', () => {
    const firstDiagram = formulaToDiagram('∀P:o. P')
    const secondDiagram = formulaToDiagram('∀P:o. ¬P')
    const thirdDiagram = formulaToDiagram('∀P:o. ¬¬P')
    const firstScene = scene3(firstDiagram)
    const secondScene = scene3(secondDiagram)
    const thirdScene = scene3(thirdDiagram)
    const expected = new SceneTweenTrack(firstScene, secondScene, 0)
    const view = mountView3(container(), { diagram: firstDiagram, theme: DARK })

    runFrame(0)
    view.update({ diagram: secondDiagram, theme: DARK })
    runFrame(0)

    const interruptedAt = SCENE_TWEEN_MS / 2
    runFrame(interruptedAt)
    const displayed = expected.sample(interruptedAt)
    expect(renderState.entityFrames.at(-1)).toEqual(displayed.entities)

    now = interruptedAt
    expected.begin(displayed, thirdScene, interruptedAt)
    view.update({ diagram: thirdDiagram, theme: DARK })
    runFrame(interruptedAt)
    expect(renderState.entityFrames.at(-1)).toEqual(expected.sample(interruptedAt).entities)

    runFrame(interruptedAt + SCENE_TWEEN_MS / 2)
    expect(renderState.entityFrames.at(-1)).toEqual(
      expected.sample(interruptedAt + SCENE_TWEEN_MS / 2).entities,
    )

    runFrame(interruptedAt + SCENE_TWEEN_MS)
    expect(renderState.entityFrames.at(-1)).toEqual(thirdScene.entities)
    view.dispose()
  })
})
