import { $, browser, expect } from '@wdio/globals'
import { describe, it } from 'mocha'
import { diagramFromJson } from '../../src/kernel/diagram'
import { focusPoint } from '../../src/view3d/pick'
import { scene3 } from '../../src/view3d/scene'
import {
  canvasOffsetForWorldPoint,
  canvas,
  clickWorld,
  dragWorld,
  displayedPose,
  expectDirectionClose,
  expectDoubleCut,
  expectPoseClose,
  game,
  hold,
  poseEyeDistance,
  rightClickWorld,
  storedCameraPose,
  storedTreeDiagram,
  waitForVisibleTreeTween,
  wheelWorld,
} from './native'

describe('orchard world controls', () => {
  it('moves through free flight and orbit while persisting only the free pose', async () => {
    await expect(game()).toHaveAttribute('data-camera-mode', 'menu')
    await expect($('.slot.invalid')).toBeDisplayed()
    await expect($('.slot.invalid small')).not.toHaveText('')
    await $('[data-new-slot-name]').setValue('   ')
    await $('[data-create-slot]').click()
    await expect($('[data-menu-error]')).toHaveText('Enter a name for the new orchard.')

    await $('[data-load-slot="large-1"]').click()
    await expect(game()).toHaveAttribute('data-ready', 'true')
    await expect(game()).toHaveAttribute('data-loaded-slot', 'large-1')
    await expect(game()).toHaveAttribute('data-camera-mode', 'free')
    await expect(game()).toHaveAttribute('data-input-engaged', 'false')
    const engagePrompt = $('[data-engage]')
    await expect(engagePrompt).toBeDisplayed()
    await expect(engagePrompt).toHaveText('Click to play')
    const [promptLocation, promptSize, canvasLocation, canvasSize] = await Promise.all([
      engagePrompt.getLocation(),
      engagePrompt.getSize(),
      canvas().getLocation(),
      canvas().getSize(),
    ])
    expect(promptLocation.x + promptSize.width / 2)
      .toBeCloseTo(canvasLocation.x + canvasSize.width / 2, 0)
    expect(promptLocation.y + promptSize.height / 2)
      .toBeCloseTo(canvasLocation.y + canvasSize.height / 2, 0)
    await expect($('[data-reticle]')).not.toBeDisplayed()

    const loadedPose = await displayedPose()
    await clickWorld()
    await expect(game()).toHaveAttribute('data-input-engaged', 'true')
    await expectPoseClose(await displayedPose(), loadedPose)
    await expect($('[data-reticle]')).toBeDisplayed()
    await expect($('[data-engage]')).not.toBeDisplayed()

    await clickWorld(500, 300)
    await expect(game()).toHaveAttribute('data-camera-mode', 'orbit')
    await expect(game()).toHaveAttribute('data-orbit-target', 'tree-0000')
    await browser.keys('Escape')
    await expect(game()).toHaveAttribute('data-camera-mode', 'free')
    await expectPoseClose(await displayedPose(), loadedPose)
    await expect(game()).toHaveAttribute('data-input-engaged', 'true')

    await hold('w')
    const movedPose = await displayedPose()
    expect(poseEyeDistance(movedPose, loadedPose)).toBeGreaterThan(0.01)
    await expect(game()).toHaveAttribute('data-camera-mode', 'free')
    const preOrbitPose = movedPose

    await browser.waitUntil(() => poseEyeDistance(storedCameraPose('large-1'), preOrbitPose) < 0.000_001)
    await expect(game()).toHaveAttribute('data-save-state', 'idle')
    const diagramBeforeDoubleCut = storedTreeDiagram('large-1', 'tree-0000')
    await clickWorld()
    await expect(game()).toHaveAttribute('data-camera-mode', 'orbit')
    await expect(game()).toHaveAttribute('data-orbit-target', 'tree-0000')
    await expect(game()).toHaveAttribute('data-input-engaged', 'false')
    await expect($('[data-reticle]')).not.toBeDisplayed()
    await expect($('[data-engage]')).not.toBeDisplayed()
    expect((await canvas().getCSSProperty('cursor')).value).toBe('auto')
    expect(storedTreeDiagram('large-1', 'tree-0000')).toEqual(diagramBeforeDoubleCut)

    const orbitPose = await displayedPose()
    const savedFreePose = storedCameraPose('large-1')
    await dragWorld(0, { x: -30, y: -20 }, { x: 45, y: 25 })
    await browser.pause(100)
    const movedOrbitPose = await displayedPose()
    expect(poseEyeDistance(movedOrbitPose, orbitPose)).toBeGreaterThan(0.01)
    expectPoseClose(storedCameraPose('large-1'), savedFreePose)

    await wheelWorld(-320)
    await browser.pause(100)
    const zoomedOrbitPose = await displayedPose()
    expect(poseEyeDistance(zoomedOrbitPose, movedOrbitPose)).toBeGreaterThan(0.01)
    expectPoseClose(storedCameraPose('large-1'), savedFreePose)

    const semanticScene = scene3(diagramFromJson(diagramBeforeDoubleCut))
    const branchFocuses = semanticScene.entities.flatMap((entity) => {
      if (entity.kind !== 'branch') return []
      const focus = focusPoint(entity.key, semanticScene.entities)
      return focus === null ? [] : [{ entity, focus }]
    }).sort((a, b) => {
      const distance = ({ focus }: typeof a): number => Math.hypot(
        focus.x - semanticScene.center.x,
        focus.y - semanticScene.center.y,
        focus.z - semanticScene.center.z,
      )
      return distance(b) - distance(a)
    })
    const offCenterBranch = branchFocuses[0]
    if (offCenterBranch === undefined) throw new Error('fixture has no branch to focus')
    const focusOffset = await canvasOffsetForWorldPoint(zoomedOrbitPose, offCenterBranch.focus)
    await clickWorld(focusOffset.x, focusOffset.y)
    await browser.pause(300)
    const focusedOrbitPose = await displayedPose()
    for (const axis of ['x', 'y', 'z'] as const) {
      const translation = offCenterBranch.focus[axis] - semanticScene.center[axis]
      expect(focusedOrbitPose.eye[axis]).toBeCloseTo(zoomedOrbitPose.eye[axis] + translation, 6)
      expect(focusedOrbitPose.direction[axis]).toBeCloseTo(zoomedOrbitPose.direction[axis], 6)
    }

    await dragWorld(2, { x: -20, y: 15 }, { x: 35, y: -25 })
    await browser.pause(100)
    const pannedOrbitPose = await displayedPose()
    expect(poseEyeDistance(pannedOrbitPose, focusedOrbitPose)).toBeGreaterThan(0.01)
    expect(storedTreeDiagram('large-1', 'tree-0000')).toEqual(diagramBeforeDoubleCut)

    const beforeToolPose = pannedOrbitPose
    const toolOffset = await canvasOffsetForWorldPoint(pannedOrbitPose, offCenterBranch.focus)
    await rightClickWorld(toolOffset.x, toolOffset.y)
    await expect($('[data-feedback]')).toHaveText('Double cut applied to tree-0000.')
    await waitForVisibleTreeTween()
    const diagramAfterDoubleCut = storedTreeDiagram('large-1', 'tree-0000')
    expectDoubleCut(
      diagramBeforeDoubleCut,
      diagramAfterDoubleCut,
      offCenterBranch.entity.region,
    )
    await expect(game()).toHaveAttribute('data-camera-mode', 'orbit')
    await expect(game()).toHaveAttribute('data-orbit-target', 'tree-0000')
    await expectPoseClose(await displayedPose(), beforeToolPose)

    await browser.keys('Escape')
    await expect(game()).toHaveAttribute('data-camera-mode', 'free')
    await expect(game()).toHaveAttribute('data-input-engaged', 'true')
    await expectPoseClose(await displayedPose(), preOrbitPose)

    await hold('w')
    const finalPose = await displayedPose()
    expect(poseEyeDistance(finalPose, preOrbitPose)).toBeGreaterThan(0.01)
    expectDirectionClose(finalPose, preOrbitPose)
    await browser.waitUntil(() => poseEyeDistance(storedCameraPose('large-1'), finalPose) < 0.000_001)
    await expect(game()).toHaveAttribute('data-save-state', 'idle')
    await expectPoseClose(storedCameraPose('large-1'), finalPose)
    expect(storedTreeDiagram('large-1', 'tree-0000')).toEqual(diagramAfterDoubleCut)
  })
})
