import { $, $$, browser, expect } from '@wdio/globals'
import { describe, it } from 'mocha'
import { Key } from 'webdriverio'
import type { TutorialMilestoneId } from '../../src/game/tutorial'
import { diagramFromJson } from '../../src/kernel/diagram'
import { scene3 } from '../../src/view3d/scene'
import {
  aimReticleAt,
  attribute,
  canvasOffsetForWorldPoint,
  canvasScreenshot,
  clickWorld,
  createSlot,
  displayedPose,
  game,
  hold,
  lookReticleAt,
  moveDesktopPointer,
  moveFreeCameraTo,
  rightClickWorld,
  storedOrder,
  storedReputation,
  storedTree,
  storedTreeDiagram,
  storedTreeIds,
  storedTutorialProgress,
  waitForMenu,
  waitForVisibleTreeTween,
} from './native'

type OpeningTool = 'sprout-spawner' | 'double-cut' | 'iteration'
type Point = { readonly x: number; readonly z: number }

async function waitForSave(): Promise<void> {
  await expect(game()).toHaveAttribute('data-save-state', 'idle')
}

async function completedMilestones(): Promise<readonly string[]> {
  return JSON.parse(await attribute('completed-tutorial-milestones')) as readonly string[]
}

async function expectInstruction(milestoneId: TutorialMilestoneId): Promise<void> {
  const card = $('[data-tutorial-card]')
  const instruction = $('[data-tutorial-instruction]')
  await expect(card).toBeDisplayed()
  await expect(card).toHaveAttribute('data-tutorial-milestone', milestoneId)
  await expect($$('[data-tutorial-instruction]')).toBeElementsArrayOfSize(1)
  await expect(instruction).toBeDisplayed()
  expect((await instruction.getText()).trim().length).toBeGreaterThan(0)
  await expect($('[data-tutorial-checklist]')).not.toExist()
  await expect($('[data-tutorial-progress]')).not.toExist()
}

async function expectInstructionAbsent(): Promise<void> {
  const card = $('[data-tutorial-card]')
  await expect(card).not.toBeDisplayed()
  expect(await card.getAttribute('data-tutorial-milestone')).toBeNull()
  await expect($('[data-tutorial-instruction]')).not.toBeDisplayed()
}

async function setTutorials(enabled: boolean): Promise<void> {
  await browser.keys('Escape')
  await expect($('[data-pause]')).toBeDisplayed()
  await $('[data-pause-settings]').click()
  await expect($('[data-settings]')).toBeDisplayed()
  const checkbox = $('[data-settings-tutorials]')
  if (await checkbox.isSelected() !== enabled) await checkbox.click()
  await expect(game()).toHaveAttribute('data-tutorials-enabled', String(enabled))
  await $('[data-settings-back]').click()
  await expect($('[data-pause]')).toBeDisplayed()
  await $('[data-pause-resume]').click()
  await expect(game()).toHaveAttribute('data-paused', 'false')
}

async function openLedger(tab: 'tools' | 'orders'): Promise<void> {
  await browser.keys('Tab')
  await expect($('[data-ledger]')).toBeDisplayed()
  if (await attribute('ledger-tab') !== tab) await $(`[data-ledger-primary="${tab}"]`).click()
  await expect(game()).toHaveAttribute('data-ledger-tab', tab)
}

async function acquire(toolId: 'double-cut' | 'iteration'): Promise<void> {
  const action = $(`[data-tool-id="${toolId}"] [data-tool-action="acquire"]`)
  await action.waitForDisplayed()
  await action.click()
  await expect(game()).toHaveAttribute('data-selected-tool', toolId)
}

async function selectTool(toolId: OpeningTool): Promise<void> {
  for (let attempt = 0; attempt < 4; attempt++) {
    if (await attribute('selected-tool') === toolId) return
    await browser.keys('1')
  }
  await expect(game()).toHaveAttribute('data-selected-tool', toolId)
}

async function acceptOrder(orderId: string, view: { readonly x: number; readonly z: number }): Promise<void> {
  await moveFreeCameraTo({ ...view, y: 1.7 })
  await openLedger('orders')
  const action = $(`[data-order-id="${orderId}"] [data-order-action="accept"]`)
  await action.waitForDisplayed()
  await action.click()
  await expect($('[data-feedback]')).toHaveText(`Accepted ${orderId}.`)
  await waitForSave()
}

async function takeWholeTree(slotId: string, treeId: string): Promise<void> {
  await selectTool('iteration')
  const tree = storedTree(slotId, treeId)
  await aimReticleAt(visibleBranchWorldPoint(tree, tree.diagram.root))
  await rightClickWorld()
  await expect(game()).toHaveAttribute('data-cutting-held', 'true')
  await expect($('[data-feedback]')).toHaveText(expect.stringContaining('Whole-tree cutting held from'))
}

async function deliver(slotId: string, orderId: string, sourceId: string): Promise<void> {
  await takeWholeTree(slotId, sourceId)
  const pot = storedOrder(slotId, orderId).pot
  if (pot === null) throw new Error(`order '${orderId}' has no accepted pot`)
  await aimReticleAt({ x: pot.x + 0.85, y: 0.55, z: pot.z })
  await rightClickWorld()
  await expect($('[data-feedback]')).toHaveText(expect.stringContaining(`Completed ${orderId}.`))
  await expect(game()).toHaveAttribute('data-cutting-held', 'false')
  await waitForSave()
}

async function duplicateTree(slotId: string, sourceId: string, target: Point): Promise<string> {
  const beforeIds = storedTreeIds(slotId)
  await takeWholeTree(slotId, sourceId)
  await aimReticleAt({ ...target, y: -0.035 })
  await rightClickWorld()
  await expect($('[data-feedback]')).toHaveText(expect.stringContaining('Duplicated tree as tree-'))
  await browser.waitUntil(() => storedTreeIds(slotId).length === beforeIds.length + 1)
  const duplicateId = storedTreeIds(slotId).find((id) => !beforeIds.includes(id))
  if (duplicateId === undefined) throw new Error('duplicate did not receive a fresh ID')
  return duplicateId
}

function nestedCutRegions(diagram: ReturnType<typeof storedTreeDiagram>): {
  readonly outer: string
  readonly inner: string
} {
  const outer = Object.entries(diagram.regions).find(([, region]) => (
    region.kind === 'cut' && region.parent === diagram.root
  ))?.[0]
  if (outer === undefined) throw new Error('diagram has no outer cut')
  const inner = Object.entries(diagram.regions).find(([, region]) => (
    region.kind === 'cut' && region.parent === outer
  ))?.[0]
  if (inner === undefined) throw new Error('diagram has no inner cut')
  return { outer, inner }
}

async function doubleCutRegion(slotId: string, treeId: string, regionId: string): Promise<void> {
  await selectTool('double-cut')
  const before = storedTree(slotId, treeId)
  const selectionPoint = visibleBranchWorldPoint(before, before.diagram.root)
  await moveFreeCameraTo({ x: before.x + 6, y: 2, z: before.z + 6 })
  await lookReticleAt(selectionPoint)
  await clickWorld()
  await expect(game()).toHaveAttribute('data-camera-mode', 'orbit')
  await expect(game()).toHaveAttribute('data-orbit-target', treeId)

  const world = visibleBranchWorldPoint(before, regionId)
  const offset = await canvasOffsetForWorldPoint(await displayedPose(), world)
  const beforeFrame = await canvasScreenshot()
  await rightClickWorld(offset.x, offset.y)
  await expect($('[data-feedback]')).toHaveText(`Double cut applied to ${treeId}.`)
  await browser.waitUntil(() => Object.keys(storedTreeDiagram(slotId, treeId).regions).length
    === Object.keys(before.diagram.regions).length + 2)
  await waitForVisibleTreeTween(beforeFrame)
  await browser.keys('Backspace')
  await expect(game()).toHaveAttribute('data-camera-mode', 'free')
}

async function iterateWithinTree(
  slotId: string,
  treeId: string,
  sourceRegionId: string,
  targetRegionId: string,
): Promise<void> {
  await selectTool('iteration')
  const before = storedTree(slotId, treeId)
  if (await attribute('camera-mode') !== 'orbit' || await attribute('orbit-target') !== treeId) {
    await moveFreeCameraTo({ x: before.x + 6, y: 2, z: before.z + 6 })
    await lookReticleAt(visibleBranchWorldPoint(before, before.diagram.root))
    await clickWorld()
  }
  await expect(game()).toHaveAttribute('data-camera-mode', 'orbit')
  await expect(game()).toHaveAttribute('data-orbit-target', treeId)

  const pose = await displayedPose()
  const source = await canvasOffsetForWorldPoint(pose, visibleBranchWorldPoint(before, sourceRegionId))
  const target = await canvasOffsetForWorldPoint(pose, visibleBranchWorldPoint(before, targetRegionId))
  const beforeFrame = await canvasScreenshot()
  await rightClickWorld(source.x, source.y)
  await expect($('[data-feedback]')).toHaveText(expect.stringContaining(`Subtree cutting held from ${treeId}.`))
  await rightClickWorld(target.x, target.y)
  await expect($('[data-feedback]')).toHaveText(`Iteration applied to ${treeId}.`)
  await browser.waitUntil(() => Object.keys(storedTreeDiagram(slotId, treeId).regions).length
    > Object.keys(before.diagram.regions).length)
  await waitForVisibleTreeTween(beforeFrame)
  await browser.keys('Backspace')
  await expect(game()).toHaveAttribute('data-camera-mode', 'free')
}

function visibleBranchWorldPoint(
  tree: ReturnType<typeof storedTree>,
  regionId: string,
): { readonly x: number; readonly y: number; readonly z: number } {
  const scene = scene3(diagramFromJson(tree.diagram))
  const branch = scene.entities.find((entity) => entity.kind === 'branch' && entity.region === regionId)
  if (branch?.kind !== 'branch') throw new Error(`region '${regionId}' has no visible branch`)
  const segment = branch.pts.slice(1).map((end, index) => ({
    start: branch.pts[index]!,
    end,
  })).sort((a, b) => Math.hypot(
    b.end.x - b.start.x,
    b.end.y - b.start.y,
    b.end.z - b.start.z,
  ) - Math.hypot(
    a.end.x - a.start.x,
    a.end.y - a.start.y,
    a.end.z - a.start.z,
  ))[0]
  if (segment === undefined) throw new Error(`region '${regionId}' has no visible segment`)
  const local = {
    x: (segment.start.x + segment.end.x) / 2,
    y: (segment.start.y + segment.end.y) / 2,
    z: (segment.start.z + segment.end.z) / 2,
  }
  const cosine = Math.cos(tree.yaw)
  const sine = Math.sin(tree.yaw)
  return {
    x: tree.x + local.x * cosine + local.z * sine,
    y: local.y,
    z: tree.z - local.x * sine + local.z * cosine,
  }
}

describe('opening tutorial progression', () => {
  it('requires whole-tree duplication and then a same-tree iteration before opening the first order', async () => {
    const slotId = await createSlot('Two Iteration Lessons', false)
    await openLedger('tools')
    await acquire('double-cut')
    await acquire('iteration')
    await browser.keys('Tab')
    await setTutorials(true)

    await selectTool('double-cut')
    await clickWorld()
    await expect(game()).toHaveAttribute('data-camera-mode', 'orbit')
    const beforeCut = storedTree(slotId, 'tree-0000')
    const cutTarget = await canvasOffsetForWorldPoint(
      await displayedPose(),
      visibleBranchWorldPoint(beforeCut, beforeCut.diagram.root),
    )
    await rightClickWorld(cutTarget.x, cutTarget.y)
    await expect($('[data-feedback]')).toHaveText('Double cut applied to tree-0000.')
    await browser.waitUntil(() => Object.keys(storedTreeDiagram(slotId, 'tree-0000').regions).length === 3)

    await selectTool('iteration')
    const doubleCutTree = storedTree(slotId, 'tree-0000')
    const wholeTree = await canvasOffsetForWorldPoint(
      await displayedPose(),
      visibleBranchWorldPoint(doubleCutTree, doubleCutTree.diagram.root),
    )
    await rightClickWorld(wholeTree.x, wholeTree.y)
    await expect($('[data-feedback]')).toHaveText('Whole-tree cutting held from tree-0000.')
    const ground = await canvasOffsetForWorldPoint(await displayedPose(), { x: 6, y: -0.035, z: 0 })
    await rightClickWorld(ground.x, ground.y)
    await expect($('[data-feedback]')).toHaveText(expect.stringContaining('Duplicated tree as tree-'))
    await browser.waitUntil(() => storedTreeIds(slotId).length === 2)
    expect(storedTutorialProgress(slotId).completed).toContain('duplicate-nonblank')

    await openLedger('orders')
    await expect($('[data-order-id="blank-sprout"]')).not.toExist()
    await browser.keys('Tab')

    const beforeIteration = storedTree(slotId, 'tree-0000')
    const cuts = nestedCutRegions(beforeIteration.diagram)
    await iterateWithinTree(slotId, 'tree-0000', cuts.outer, beforeIteration.diagram.root)
    expect(storedTutorialProgress(slotId).completed).toContain('iterate-within-tree')

    await openLedger('orders')
    await expect($('[data-order-id="blank-sprout"]')).toBeDisplayed()
    await browser.keys('Tab')
    await browser.keys('Escape')
    await $('[data-pause-main-menu]').click()
    await waitForMenu()
  })

  it('drives every instruction and completes the final two orders in either sequence', async () => {
    const slotId = await createSlot('Tutorial Progression')
    await expect(game()).toHaveAttribute('data-tutorials-enabled', 'true')
    await expectInstruction('move')

    await hold('w', 140)
    await expectInstruction('look')

    await setTutorials(false)
    await expectInstructionAbsent()
    const beforeLook = await displayedPose()
    for (const [x, y] of [[24, -12], [-16, 9], [31, 7], [-11, -15]] as const) {
      await moveDesktopPointer(x, y)
      if ((await displayedPose()).direction.x !== beforeLook.direction.x) break
    }
    await browser.waitUntil(async () => (await displayedPose()).direction.x !== beforeLook.direction.x, {
      timeoutMsg: 'native pointer movement did not change the free-flight look direction',
    })
    await browser.waitUntil(async () => (await completedMilestones()).includes('look'))
    expect((await displayedPose()).direction).not.toEqual(beforeLook.direction)
    expect(storedTutorialProgress(slotId).enabled).toBe(false)

    await setTutorials(true)
    await expectInstruction('ascend')
    expect(storedTutorialProgress(slotId).completed).toContain('look')

    await hold(Key.Space, 120)
    await expectInstruction('descend')
    await hold(Key.Control, 120)
    await expectInstruction('sprint')
    await browser.action('key')
      .down(Key.Shift).down('w').pause(140).up('w').up(Key.Shift).perform()
    await expectInstruction('select-tree')

    await aimReticleAt({ x: 0, y: 0.25, z: 0 })
    await clickWorld()
    await expect(game()).toHaveAttribute('data-camera-mode', 'orbit')
    await expectInstruction('move-orbit')
    await hold('a', 120)
    await expectInstruction('exit-orbit')
    await browser.keys('Backspace')
    await expect(game()).toHaveAttribute('data-camera-mode', 'free')
    await expectInstruction('spawn-two-sprouts')

    await selectTool('sprout-spawner')
    const initialIds = storedTreeIds(slotId)
    await aimReticleAt({ x: 1, y: -0.035, z: 0 })
    await rightClickWorld()
    await expect($('[data-feedback]')).toHaveText(expect.stringContaining('too close'))
    expect(storedTreeIds(slotId)).toEqual(initialIds)

    for (const [index, point] of ([{ x: -8, z: 0 }, { x: 8, z: 0 }] as const).entries()) {
      await aimReticleAt({ ...point, y: -0.035 })
      await rightClickWorld()
      await expect($('[data-feedback]')).toHaveText(expect.stringContaining('Planted sprout tree-'))
      await browser.waitUntil(() => storedTreeIds(slotId).length === initialIds.length + index + 1)
    }
    expect(storedTreeIds(slotId)).toHaveLength(3)
    const planted = storedTreeIds(slotId)
      .filter((id) => id !== 'tree-0000')
      .map((id) => storedTree(slotId, id))
      .sort((a, b) => a.x - b.x)
    const leftSprout = planted[0]
    if (leftSprout === undefined) throw new Error('left planted sprout is missing')
    await expectInstruction('acquire-double-cut')

    await openLedger('tools')
    await acquire('double-cut')
    await expectInstruction('apply-double-cut')
    await browser.keys('Tab')
    await doubleCutRegion(slotId, 'tree-0000', storedTreeDiagram(slotId, 'tree-0000').root)
    await expectInstruction('double-cut-explained')

    await setTutorials(false)
    await openLedger('tools')
    await browser.keys('Tab')
    await setTutorials(true)
    await expectInstruction('acquire-iteration')
    await waitForSave()
    expect(storedTutorialProgress(slotId).completed).toContain('double-cut-explained')

    await openLedger('tools')
    await expectInstruction('acquire-iteration')
    await acquire('iteration')
    await browser.keys('Tab')
    await expectInstruction('duplicate-nonblank')

    const tutorialDuplicateId = await duplicateTree(slotId, 'tree-0000', { x: 0, z: -8 })
    await expectInstruction('iterate-within-tree')
    const doubleCut = nestedCutRegions(storedTreeDiagram(slotId, 'tree-0000'))
    await iterateWithinTree(
      slotId,
      'tree-0000',
      doubleCut.outer,
      storedTreeDiagram(slotId, 'tree-0000').root,
    )
    await expectInstruction('complete-blank-order')

    await acceptOrder('blank-sprout', { x: -12, z: 12 })
    await deliver(slotId, 'blank-sprout', leftSprout.id)
    await expectInstructionAbsent()
    expect(storedOrder(slotId, 'blank-sprout')).toEqual({ state: 'completed', pot: null })

    await acceptOrder('single-double-cut', { x: 0, z: 14 })
    await deliver(slotId, 'single-double-cut', tutorialDuplicateId)
    expect(storedOrder(slotId, 'single-double-cut')).toEqual({ state: 'completed', pot: null })

    const finalBId = await duplicateTree(slotId, 'tree-0000', { x: 8, z: -8 })
    const tutorialDuplicateCuts = nestedCutRegions(storedTreeDiagram(slotId, tutorialDuplicateId))
    const finalBCuts = nestedCutRegions(storedTreeDiagram(slotId, finalBId))
    await doubleCutRegion(slotId, tutorialDuplicateId, tutorialDuplicateCuts.outer)
    await doubleCutRegion(slotId, finalBId, finalBCuts.inner)

    await moveFreeCameraTo({ x: 14, y: 1.7, z: 14 })
    await openLedger('orders')
    const finalAvailable: Array<string | null> = []
    for (const element of await $$('[data-order-id]')) {
      finalAvailable.push(await element.getAttribute('data-order-id'))
    }
    expect(new Set(finalAvailable)).toEqual(new Set([
      'irregular-double-cut-a',
      'irregular-double-cut-b',
    ]))
    await $(`[data-order-id="irregular-double-cut-b"] [data-order-action="accept"]`).click()
    await waitForSave()
    await acceptOrder('irregular-double-cut-a', { x: -14, z: 14 })

    await deliver(slotId, 'irregular-double-cut-b', finalBId)
    await deliver(slotId, 'irregular-double-cut-a', tutorialDuplicateId)
    expect(storedOrder(slotId, 'irregular-double-cut-a')).toEqual({ state: 'completed', pot: null })
    expect(storedOrder(slotId, 'irregular-double-cut-b')).toEqual({ state: 'completed', pot: null })
    expect(storedReputation(slotId)).toBe(4)
    expect(new Set(storedTutorialProgress(slotId).completed)).toEqual(new Set([
      'move', 'look', 'ascend', 'descend', 'sprint', 'select-tree', 'move-orbit', 'exit-orbit',
      'spawn-two-sprouts', 'acquire-double-cut', 'apply-double-cut', 'double-cut-explained',
      'acquire-iteration', 'duplicate-nonblank', 'iterate-within-tree', 'complete-blank-order',
      'complete-single-double-cut-order', 'complete-irregular-double-cut-a-order',
      'complete-irregular-double-cut-b-order',
    ]))
    expect(await attribute('errors')).toBe('')
  })
})
